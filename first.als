abstract sig File {
	name : one Name,
    version : one Version,
	location : one Location
}

abstract sig Location {

}

sig R extends Location {}

sig L extends Location {}

sig Version {}

sig Name { } 

abstract sig FileSystem {
	files: set File,
	index: Name -> one File
} {
//	all f : files | f.name not in (files - f).name
//	all f : files | f.name.index.name = f.name
//	Name.index = files
	Name.index = files
}


sig Repository extends FileSystem {
	
} {
	all f :files | f.location = R
}

sig Local extends FileSystem {
} {
	all f : files | f.location = L
}

fact {
	FileSystem.files = File
	all n : Name | n in File.name
	all v : Version | v in File.version
    all fs :FileSystem | all disj n, n' : Name.(fs.index) | n != n'
    all fs :FileSystem | all disj f, f' : (fs.index).File | f != f'
}

fun lookup (fs: FileSystem, n: Name): File {
    n.(fs.index)
}

run {}

pred updateLocal(l, l' : Local, f, f' : File) {
	f. name = f'.name
    f.version != f'.version
	l'.files = l.files - f + f'
	l'.index = l.index - (f.name -> f) + (f'.name -> f')
//     f in l.files 
}

run updateLocal for 4 but exactly 2 Local, 0 Repository

pred updateRepository(r, r' : Repository, f, f', f'' : File) {
	f.location = L
	f'.location = R
	f''.location = R
	f.name = f'.name
	f.name = f''.name
    f.version != f'.version
	f.version = f''.version
	r'.files = r.files - f' + f''
	r'.index = r.index - (f'.name -> f') + (f''.name -> f'')
//     f in l.files 
}



pred commit(l, l': Local, r, r':Repository) {
	all f : l'.files - l.files | one f' : r.files | one f'' : r'.files | updateRepository[r, r', f, f', f'']
	l.files.name = r.files.name
	l'.files.name = r'.files.name
	#(l'.files - l.files) > 0
}

run commit

run commit for 10 but exactly 2 Local,exactly  2 Repository

assert FileNameIsUniqueInLocal {
	all l : FileSystem | all f: l.files, n : f.name | n not in (l.files -f).name
}

check FileNameIsUniqueInLocal
