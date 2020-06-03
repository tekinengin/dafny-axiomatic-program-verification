datatype Tree<T> = Leaf | Node(Tree<T>, Tree<T>, T)
datatype List<T> = Nil | Cons(T, List<T>)

function flatten<T>(tree:Tree<T>):List<T>

{
	match tree
    case Leaf => Nil
    case Node(l_tree,r_tree,v) => Cons(v,append(flatten(l_tree),flatten(r_tree)))

}

function append<T>(xs:List<T>, ys:List<T>):List<T>
{
	match xs
    case Nil => ys
    case Cons(x,xs') => Cons(x, append(xs',ys))
}

function treeContains<T>(tree:Tree<T>, element:T):bool
{
    match tree
    case Leaf => false
    case Node(l_tree, r_tree, v) => treeContains(l_tree,element) || treeContains(r_tree,element) || (v == element) 
}

function listContains<T>(xs:List<T>, element:T):bool
{
	match xs
    case Nil => false
    case Cons(x,xs') => (x == element) || listContains(xs', element)
}


lemma sameElements<T>(tree:Tree<T>, element:T)
ensures treeContains(tree, element) <==> listContains(flatten(tree), element)
{
    match tree
    case Leaf => {}
    case Node (l_tree,r_tree,v) => {
              calc{treeContains(Node(l_tree,r_tree,v),element);
        == treeContains(l_tree,element) || treeContains(r_tree,element) || (v==element);
        == {sameElements(l_tree,element);
           sameElements(r_tree,element);}
        listContains(flatten(l_tree),element) || listContains(flatten(r_tree),element) || (v==element);
        == listContains(Cons(v,append(flatten(l_tree),flatten(r_tree))),element);
        == listContains(flatten(tree), element);
        }      
    }  
}
