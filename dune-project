(lang dune 3.21)
(using rocq 0.11)

(name euclidean)

(generate_opam_files true)

(source
 (github ngover05/euclidean))

(authors
 "Nicholas Gover <nicholasgover99@gmail.com>")

(maintainers
 "Nicholas Gover <nicholasgover99@gmail.com>")

(license )

(documentation https://github.com/ngover05/euclidean)

(package
 (name euclidean)
 (synopsis "idk")
 (description "Extended Euclidean Algorithm verified. For CSG Dragonlab")
 (depends
   (dune (>= 3.21.0))
   (rocq (>= 9.0.0))))
