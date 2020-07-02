# dafny-axiomatic-program-verification
This repo is an example of Dafny Axiomatic Program Verification. 

This code ensures that given:

datatype Tree<T> = Leaf | Node(Tree<T>, Tree<T>, T)
datatype List<T> = Nil | Cons(T, List<T>)

treeContains(tree, element) <==> listContains(flatten(tree), element)

by using dafny programming language.
