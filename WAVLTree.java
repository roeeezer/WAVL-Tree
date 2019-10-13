import java.util.Arrays;
import java.util.HashSet;
import java.util.Random;
import java.util.concurrent.ThreadLocalRandom;

/**
 *
 * WAVLTree
 *
 * An implementation of a WAVL Tree. (Haupler, Sen & Tarajan '15)
 * 
 * Authors:
 * Roee Ezer, id: 312493281, username: roeeezer
 * Dvir Salomon, id: 203445036, username: dvirsalomon
 *
 */

public class WAVLTree {

	public enum NodeDirection {
        Right, Left
    }

	/**Roee:
	 * @inv node.rank!=-1 --> node.left!=null and node.right!= null
	 * 
	 * **/
	private WAVLNode externalNode = new WAVLNode(-1,null);
	private WAVLNode root;
	private WAVLNode min = null, max = null;
	
	
	/**
	 * Empty Constractor. Initializing an empty tree
	 */
	public WAVLTree() {
		this.externalNode.rank = -1;
		this.root = this.externalNode;
		this.min = this.root;
        this.max = this.root;
	}
	
	/**
	 * Constractor. Initializing a tree with root with key and info
	 * @param key - the key of the root
	 * @param info - the info of the root
	 */
	public WAVLTree(int key,String info) {
		this.externalNode.rank = -1;
		WAVLNode root = new WAVLNode(key,info);
		this.root = root;
		root.left = externalNode;
		root.right = externalNode;
		root.rank = 0;
		root.updateSubtreeSize(); // Dvir: ==1
		this.min = this.root;
		this.max = this.root;
		
	}
	
	/**
	 * Returns a WAVLNode with key k and info i
	 * @param k - the key of the node
	 * @param i - the info of the root
	 * @return WAVLNode with key and info
	 */
	public WAVLNode createWavlNode(int k,String i){
		return new WAVLNode(k,i);
		
	}
	


	/**
	 * public boolean empty()
	 *
	 * Dvir: Checks whether the tree is empty or not
	 * @return returns true if and only if the tree is empty
	 */
	public boolean empty() {
		return root.rank==-1; // to be replaced by student code
	}

	/**
	 * Dvir: Searches for node with key k
	 * @param k - key
	 * @return returns the info of an item with key k if it exists in the tree otherwise,
	 * returns null
	 */
	public String search(int k) {
		if (min.key<=k && k<=max.key && !empty())
		{
			WAVLNode searchRes = search(k ,root);
			if (searchRes.key == k)
				return searchRes.info;
		}
		return null; // to be replaced by student code
	}
	
	/**
	 * Dvir: Searches for node with key k in subtree x
	 * @pre min.key<=k && k<=max.key && !empty()
	 * @post $ret == leaf or unary node
	 * @param k - key
	 * @param x - subtree
	 * @return returns WAVLNode with key k if exists, otherwise, returns the node which k should be its child
	 */
	private WAVLNode search(int k, WAVLNode x) {
		if (x.key == k) {
			return x;
		}
		else if (x.key<k) {
			if (x.right.rank>-1)
				return search(k, x.right);
			else
				return x;
		}
		else { // x.key>k
			if (x.left.rank>-1)
				return search(k, x.left);
			else
				return x;
		}
	}

	/**
	 * public int insert(int k, String i)
	 *
	 * inserts an item with key k and info i to the WAVL tree. the tree must remain
	 * valid (keep its invariants). returns the number of rebalancing operations, or
	 * 0 if no rebalancing operations were necessary. returns -1 if an item with key
	 * k already exists in the tree.
	 */
	public int insert(int k, String i) {
		//###insertion start
		WAVLNode newNode = new WAVLNode(k,i);
		newNode.left = this.externalNode;
		newNode.right = this.externalNode;
		newNode.rank = 0;
		newNode.updateSubtreeSize(); // Dvir: ==1
		
		if(this.root == this.externalNode){//empty tree
			this.root = newNode;
			this.min = newNode;
            this.max = newNode;
			return 0;
		}
		
		// maintain min and max
		if (min.getKey() > k) {
            this.min = newNode;
        }
        
        if (max.getKey() < k) {
            this.max = newNode;
        }
		
		WAVLNode parent = SearchForInsert(this.root,k);//parent must be leaf or unary node
		if(parent.key== k){// the key already exist in the tree
			return -1;
		}
		if(parent.key> k){
			parent.left = newNode;
		}
		if(parent.key< k){
			parent.right = newNode;
		}
		newNode.parent = parent;
		//###insertion done
		
		//###initial insertion balance start
		int BalancingCounter=0;
		String initCase = initialInsertionCase(newNode);//== A or B (from slide 18)
		if(initCase=="B"){
			//parent.updateSubtreeSize(); // Dvir: update subtreeSize
			updateSubtreeSizeToRoot(newNode);
			return 0;
		}
		//now we are in case A
		
		BalancingCounter+=promote(parent);
		//###initial insertion balance done
		
		//###balancing the tree start
		BalancingCounter+=balanceTheTreeAfterInsert(parent);
		
		updateSubtreeSizeToRoot(newNode);
		
		return BalancingCounter;
		
	}
	/**pnode or "problematic node" is the node who's upper edge might has invalid rank difference
	 * @post $ret = number of balancing operation executed in the method
	 * @post the tree "this" is valid AVL tree
	 * **/
	public int balanceTheTreeAfterInsert(WAVLNode pnode){
		int BalancingCounter = 0;
		if(pnode==this.root){
			return 0;
		}
		int bCase = BalancingCase(pnode);//==0 or 1 or 2 or 3 (from slide 23)
		if(bCase==0){//case = 0 means the parent of pnode has transformed 2,1 --> 1,1 or 1,2-->1,1
			return 0;
		}
		if(bCase==1){
			BalancingCounter+= promote(pnode.parent);
			BalancingCounter+= balanceTheTreeAfterInsert(pnode.parent);
		}
		if(bCase==2){
			BalancingCounter+=upperRotation(pnode,2);	
		}
		if(bCase==3){
			WAVLNode b;
			/*b is the child of x (or pnode) who has the higher rank
			 * in case 3 this is the child that we need to double rotate up */
			if(pnode.left.rank>pnode.right.rank){
				b = pnode.left;
			}
			else{
				/*in this case the children ranks are not supposed to be equal
				 * that would have stopped to case 0 or int the initial insertion balancing*/ 
				b = pnode.right;
			}
			BalancingCounter+=upperRotation(b,1);
			BalancingCounter+=upperRotation(b,2);
		}
		if(bCase==4){//parent is 2,1 node (to symetry)
			return 0;
		}
		
		
		return BalancingCounter;
		
	}
	/**execute a rotation just like in slide 26
	 * 
	 * @pre ind==1 or ind==2
	 * ind ==1 --> this is the first rotation in a double rotation process
	 * ind ==2 --> this is the second rotation in a double rotation process
	 * the only difference is that in ind=1 we execute x.parent.rank-- and x.rank++
	 * and in ind =2 we only execute x.parent.rank--
	 * it means that the regular rotation in case 2 (slide 26) is ind==2**/
	public int upperRotation(WAVLNode x,int ind){
		int balancingCount=1;//the rotation itself is a balancing operation
		WAVLNode z = x.parent;
		
		WAVLNode a = x.left;
		WAVLNode b = x.right;
		if(z==this.root){
			this.root = x;
		}
		else{//z is not the root
			WAVLNode grandparent = z.parent;
			replaceChild(grandparent,z,x);
		}
		
		boolean xIsLeftChild = x==z.left;
		if(xIsLeftChild){
			WAVLNode y = z.right;//right brother of x
			edgeUpdate(x,a,"L");
			edgeUpdate(x,z,"R");
			edgeUpdate(z,b,"L");
			edgeUpdate(z,y,"R");	
		}
		else{//x is right child
			WAVLNode y = z.left;//left brother of x
			edgeUpdate(x,z,"L");
			edgeUpdate(x,b,"R");
			edgeUpdate(z,y,"L");
			edgeUpdate(z,a,"R");	
		}
		//Roee:update the sizes according to children a,b,y
		updateSubtreeSizeToRoot(z);
		updateSubtreeSizeToRoot(x);
		z.rank--;
		balancingCount++;//for the demotion of z
		if(ind==1){
			x.rank++;
			balancingCount++;//for the promotion of x
		}
		
		return balancingCount;
	}
	/**execute a first rotation in double rotation process
	 * the rotation is exactly the same as upperRotation 
	 * except the ranks are updated a little bit differently
	 * note: the second rotation in double rotation is exactly
	 * the same as the regular upperRotation**/

	
	public void edgeUpdate(WAVLNode parent,WAVLNode child,String childType){
		if(childType=="L"){
			parent.left = child;
			child.parent = parent;
		}
		if(childType=="R"){
			parent.right = child;
			child.parent = parent;
		}
	}
	public void replaceChild(WAVLNode parent,WAVLNode oldChild,WAVLNode newChild){
		boolean oldChildIsLeftChild = oldChild==parent.left;
		if(oldChildIsLeftChild){
			parent.left = newChild;
			newChild.parent = parent;
			oldChild.parent = null;
		}
		else{
			parent.right = newChild;
			newChild.parent = parent;
			oldChild.parent = null;
		}
	}
	/**the balancing case according to slide 23
	 * case = 0 means the parent of pnode has transformed 2,1 --> 1,1 or 1,2-->1,1
	 * case = 4 means the parent of pnode has transformed 2,2-->2,1 to symmetry (can happen only after deletions)
	 * check:V**/
	public int BalancingCase(WAVLNode pnode){
		WAVLNode parent = pnode.parent;
		int[] parentType = nodeType(parent);
		int parentDelta = Math.abs(parentType[1]-parentType[0]);
		if(parentDelta==0){//parent is 1,1 node
			return 0;
		}
		if(parentDelta==1){
			if(Math.max(parentType[0], parentType[1])==2){//parent is 2,1 node (to symetry)
				return 4;
			}
			return 1;//parent is 0,1 node (to symetry)
		}
		else{
			if(parentDelta==2){//parent is 0,2 (to symetry)
				boolean pnodeIsLeftSon = pnode==parent.left;
				if(pnodeIsLeftSon){
					if(pnode.right.rank==parent.right.rank){
						return 2;
					}
					else{
						return 3;
					}
				}
				else{//pnode is right son
				if(pnode.left.rank==parent.left.rank){
					return 2;
				}
				else{
					return 3;
				}
				}
			}
			System.out.println("Invalid balancing case (neight 0,1 nor 0,2)");
			return -1;
		}
	}
	
	//returning 1 to add to the BalancingCounter 
	public int promote(WAVLNode node){
		node.promotion();
		return 1;
	}
	/**return the rank differences between node and it's children: 1,1 2,1 1,2
	 * **/
	public int[] nodeType(WAVLNode node){
		int[] res = new int[2];
		res[0] = node.rank-node.left.rank;
		res[1] = node.rank-node.right.rank;
		return res;
	}
	public String initialInsertionCase(WAVLNode node){
		int[] parentType = nodeType(node.parent);
		int delta = Math.abs(parentType[0]-parentType[1]);
		if(delta==1){
			return "A";
		}
		if(delta==0){
			return "B";
		}
		else{// unkown Initial insertion case - problem!
			return "X";
		}
		
	}
	
	/**Roee: the method search in the subtree of StartingNode
	 * for a node x such that x.key==k
	 * if found the method will return x
	 * if not found the method will return the node that should be the parent
	 * of a node with the key k if inserted.
	 * 
	 * @param StartingNode - the node to start the search in its subtree
	 * @param k - the key to search in StartingNode
	 * @post $ret == leaf or unary node
	 * **/
	public WAVLNode SearchForInsert(WAVLNode StartingNode,int k){
		return search(k ,StartingNode);
	}
	
	/**
	 * Updates the subtreeSize field of each node until root
	 * @param node - the node to start the updates
	 */
	private void updateSubtreeSizeToRoot(WAVLNode node) {
		node.updateSubtreeSize();
		if (node != this.root)
		{
			updateSubtreeSizeToRoot(node.parent);
		}
	}
	
	/**
	 * public int delete(int k)
	 *
	 * deletes an item with key k from the binary tree, if it is there; the tree
	 * must remain valid (keep its invariants). returns the number of rebalancing
	 * operations, or 0 if no rebalancing operations were needed. returns -1 if an
	 * item with key k was not found in the tree.
	 */
    public int delete(int k) {
        if (this.empty()) {
            return -1;
        }
     
        if (this.size() == 1 && this.getRoot().getKey() == k) {
        	// delete root
            this.min = this.externalNode;
            this.max = this.externalNode;
        } else if (k == this.min.getKey()) {
            // delete min
            this.min = this.min.successor();
        } else if (k == this.max.getKey()) {
            // delete max
        	this.max = this.max.predecessor();
        }
        return this.root.delete(k);
    }
	
	/**
	 * Dvir: Returns the info of the item with the smallest key in the tree, or null if
	 * the tree is empty
	 * @return node with minimal key or null if the tree is empty
	 * @post $ret == leaf or unary node
	 */
	public String min() {
		if (empty())
			return null;
		return min.info; // to be replaced by student code
	}

	/**
	 * public String max()
	 *
	 * Dvir: Returns the info of the item with the largest key in the tree, or null if the
	 * tree is empty
	 * @return node with maximal key or null if the tree is empty
	 * @post $ret == leaf or unary node
	 */
	public String max() {
		if (empty())
			return null;
		return max.info; // to be replaced by student code
	}

	/**
	 * public int[] keysToArray()
	 *
	 * Returns a sorted array which contains all keys in the tree, or an empty array
	 * if the tree is empty.
	 * @return Returns a sorted array which contains all keys in the tree, or an empty array if the tree is empty.
	 */
	public int[] keysToArray() {
		int[] arr = new int[size()]; // to be replaced by student code
		// saving the counter in array (new int[]{0}) is used to pass the reference to memory location of counter,
		// otherwise the counter losts the value during the recursion of getKeysWithOrder
		if (arr.length > 0)
			getKeysWithOrder(root, arr, new int[]{0});
		return arr; // to be replaced by student code
	}
	
	/**
	 * Returns a sorted array which contains all keys in the tree 
	 * @pre empty() == False
	 * @param x - the node where the key list starts from 
	 * @param arr - the array that contains the keys
	 * @param i - the array that contains the first empty cell in arr
	 * @return Returns a sorted array which contains all keys in the tree
	 */
	private void getKeysWithOrder(WAVLNode x, int[] arr, int[] i) {
		if (x.left.rank > -1)
			getKeysWithOrder(x.left, arr, i);
		arr[i[0]] = x.key;
		i[0]++;
		if (x.right.rank > -1)
			getKeysWithOrder(x.right, arr, i);
	}

	/**
	 * public String[] infoToArray()
	 *
	 * Returns an array which contains all info in the tree, sorted by their
	 * respective keys, or an empty array if the tree is empty.
	 */
	public String[] infoToArray() {
		String[] arr = new String[size()]; // to be replaced by student code
		// saving the counter in array (new int[]{0}) is used to pass the reference to memory location of counter,
		// otherwise the counter losts the value during the recursion of getInfoWithOrder
		if (arr.length > 0)
			getInfoWithOrder(root, arr, new int[]{0});
		return arr; // to be replaced by student code
	}
	
	/**
	 * Returns a sorted array which contains all infos in the tree 
	 * @pre empty() == False
	 * @param x - the node where the info list starts from 
	 * @param arr - the array that contains the infos
	 * @param i - the array that contains the first empty cell in arr
	 * @return Returns a sorted array which contains all infos in the tree
	 */
	private void getInfoWithOrder(WAVLNode x, String[] arr, int[] i) {
		// Inorder traversal gives the keys with sorted order 
		if (x.left.rank > -1)
			getInfoWithOrder(x.left, arr, i);
		arr[i[0]] = x.info;
		i[0]++;
		if (x.right.rank > -1)
			getInfoWithOrder(x.right, arr, i);
	}

	/**
	 * public int size()
	 *
	 * Dvir: Returns the number of nodes in the tree.
	 * @return Returns the number of nodes in the tree
	 */
	public int size() {
		return root.size; // to be replaced by student code
	}

	/**
	 * public WAVLNode getRoot()
	 *
	 * Dvir: Returns the root WAVL node, or null if the tree is empty
	 * @return Returns the root WAVL node, or null if the tree is empty
	 *
	 */
	public WAVLNode getRoot() {
		return root;
	}

	/**
    * public int select(int i)
    *
    * Returns the value of the i'th smallest key (return null if key not found)
    * Example 1: select(1) returns the value of the node with minimal key 
    * Example 2: select(size()) returns the value of the node with maximal key 
    * Example 3: select(2) returns the value 2nd smallest minimal node, i.e the value of the node minimal node's successor  
    *
	*/
	public String select(int i) {
		if (i<1 || i>size())
			return null;
		return select(this.root, i-1);
	}
	
	/**
	 * Returns the value of the i'th smallest key
	 * @pre i<1 || i>size()
	 * @param x - the node to start the select in its sub tree
	 * @param i - the i'th smallest key
	 * @return - the value of the node with i'th smallest key
	 */
	private String select(WAVLNode x, int i)
	{
		int leftSize = x.left.size;
		
		if (i==leftSize)
			return x.info;
		else if (i<leftSize)
			return select(x.left, i);
		else
			return select(x.right, i-leftSize-1);
	}
	
	/**
	 * Checks whether the node is a leaf or not
	 * @return True if the node is a leaf, otherwise, Returns False
	 */
	public boolean isLeaf(WAVLNode node) {
		return node.left == this.externalNode && node.right == this.externalNode;
	}
	
	/**
	 * Setting the root as newRoot
	 * @param newRoot - the node to set as the root
	 */
	private void setRoot(WAVLNode newRoot) {
        this.root = newRoot;
    }

	/**
	 * public class WAVLNode
	 */
	public class WAVLNode {
		

		private WAVLNode left;
		private WAVLNode parent;
		private WAVLNode right;
		private int rank;
		private int key;
		private String info;
		private int size;
		
		/**
		 * Constractor. Create a node with key and info
		 * @param key - the key of the node
		 * @param info - the info of the node
		 */
		public WAVLNode(int key, String info){
			this.key = key;
			this.info = info;
			this.left = null;
			this.parent = null;
			this.right = null;
			this.rank = -1;
			this.size = 0;
		}

		/**
		 * Returns the node key
		 * @return the node key
		 */
		public int getKey() {
			return key; // to be replaced by student code
		}

		/**
		 * Returns the node info
		 * @return the node info
		 */
		public String getValue() {
			return info; // to be replaced by student code
		}
		
		/**
		 * Returns the node rank
		 * @return the node rank
		 */
        public int getRank() {
            return this.rank;
        }

		/**
		 * Returns the left child of the node
		 * @return the left child of the node
		 */
		public WAVLNode getLeft() {
			return left; // to be replaced by student code
		}

		/**
		 * Returns the right child of the node
		 * @return the right child of the node
		 */
		public WAVLNode getRight() {
			return right; // to be replaced by student code
		}
		
		/**
		 * adds 1 to rank
		 */
        public void promotion() {
            this.rank++;
        }
        
        /**
         * substracts 1 to rank
         */
        public void demotion() {
            this.rank--;
        }

		/**
		 * Checks whether the node is inner node or not
		 * @return True if the node is inner node, otherwise, Returns False
		 */
		public boolean isInnerNode() {
			return rank>-1; // to be replaced by student code
		}
        
		/**
		 * Checks whether the node is external node or node
		 * @return True if the node is external node, otherwise, Returns False
		 */
        public boolean isExternalNode() {
            return !this.isInnerNode();
        }
        
        /**
         * Checks whether the node is the root or node
         * @return True if the node is the root, otherwise, Returns False
         */
        private boolean isRoot() {
            return this == getRoot();
        }
        
        /**
         * Checks whether node is a leaf or not
         * @return - True if the node is a leaf, False otherwise
         */
        private boolean isLeaf() {
            return this.getRight().isExternalNode() && this.getLeft().isExternalNode();
        }

		/**
		 * Returns the number of nodes in the subtree of the node
		 * @return the number of nodes in the subtree of the node
		 */
		public int getSubtreeSize() {
			return size; // to be replaced by student code
		}
		
		/**
		 * Updates current subtree size
		 * @pre getLeft().getSubtreeSize() and getRight().getSubtreeSize() are updated
		 */
		public void updateSubtreeSize() {
			if(this.isExternalNode()){//Roee:external leafs
				size=0;
			}
			size = left.size + right.size + 1;
		}
        
		/**
		 * Sets a new subtreeSize
		 * @param newSize - the new subtreeSize
		 */
        public void setSubtreeSize(int newSize) {
            this.size = newSize;
        }
        
        /**
         * Increases subtreeSize by 1
         */
        public void increaseSubtreeSize() {
            this.setSubtreeSize(this.size + 1);
        }
        
        /**
         * Decreases subtreeSize by 1
         */
        public void decreaseSubtreeSize() {
            this.setSubtreeSize(this.size - 1);
        }
        
        /**
         * Returns the minimum node
         * @return the minimum node
         */
        private WAVLNode getMinNode() {
            return min;
        }
        
        /**
         * Returns the maximum node
         * @return the maximum node
         */
        private WAVLNode getMaxNode() {
            return max;
        }
        
        /**
         * Returns the parent node
         * @return the parent node
         */
        private WAVLNode getParent() {
            return this.parent;
        }
        
        /**
         * Sets a new parent
         * @param node - the node to set as the parent
         */
        private void setParent(WAVLNode node) {
            if (this.isExternalNode()) {
                return;
            }
            this.parent = node;
        }
        
        /**
         * Returns the left/right child
         * @param direction - the direction of the child which the function returns
         * @return the left/right child
         */
        private WAVLNode getChild(NodeDirection direction) {
            if (direction == NodeDirection.Right) {
                return this.right;
            } else {
                return this.left;
            }
        }
        
        /**
         * Changes one of the children of node
         * @param direction - the direction of the new child
         * @param newChild - the new node to set as a child
         */
        private void setChild(NodeDirection direction, WAVLNode newChild) {
            if (!this.isExternalNode()) {
            	newChild.setParent(this);
                if (direction == NodeDirection.Right) {
                    this.right = newChild;
                } else {
                    this.left = newChild;
                }
            }
        }
        
        /**
         * Returns the item following "this" according to the sorted order of keys
         * @return the item following "this" according to the sorted order of keys
         */
        private WAVLNode successor() {
            return this.goToNode(NodeDirection.Right);
        }
        
        /**
         * Returns the last item before "this" according to the sorted order of keys
         * @return the last item before "this" according to the sorted order of keys
         */
        private WAVLNode predecessor() {
            return this.goToNode(NodeDirection.Left);
        }
        
        /**
         * Go to predeccessor/successor node
         * @param direction - left for predeccessor, right for successor
         * @return the predeccessor/successor node
         */
        private WAVLNode goToNode(NodeDirection direction) {
            NodeDirection oppositeDirection = getOppositeDirection(direction);
            if ((this == getMinNode() && direction == NodeDirection.Left) || (this == getMaxNode() && direction == NodeDirection.Right)) {
                return null;
            }
            
            if ( this.getChild(direction).isInnerNode() ) {
                
            	// find the min in the left/right subtree
                WAVLNode childNode = this.getChild(direction);
                
                while (childNode.getChild(oppositeDirection).isInnerNode()) {
                    childNode = childNode.getChild(oppositeDirection);
                }
                
                return childNode;
                
            }
            else
            {
            	
                // find the first node that is a left/right child
                WAVLNode parentNode = this;
                
                while (direction == parentNode.getParentDirection()) {
                    parentNode = parentNode.parent;
                }
                
                return parentNode.parent;
            }
        }
        
        /**
         * Switches "this" node with other node 
         * @param other - the node to switch with
         */
        private void switchNode(WAVLNode other) {
        	WAVLNode x = other;
        	WAVLNode xParent = other.getParent();
        	
        	WAVLNode z = this;
            WAVLNode zParent = z.getParent();
            
            x.rank = z.getRank();
            NodeDirection zParentDirection = z.isRoot() ? null : z.getParentDirection();
            
            if (z != xParent) {
            	WAVLNode rightChildx = x.getRight();
                x.setChild(NodeDirection.Right, z.getRight());
                x.setChild(NodeDirection.Left, z.getLeft());
                z.setChild(NodeDirection.Right, rightChildx);
                z.setChild(NodeDirection.Left, externalNode);
                xParent.setChild(NodeDirection.Left, z);
            }
            else
            {
            	WAVLNode xRight = x.getRight();
                z.setChild(NodeDirection.Right, externalNode);
                x.setChild(NodeDirection.Right, z);
                x.setChild(NodeDirection.Left, z.getLeft());
                z.setChild(NodeDirection.Right, xRight);
            }
            

            
            if (!this.isRoot())
            {
            	zParent.setChild(zParentDirection, x);
            }
            else
            {
            	x.setParent(null);
                setRoot(x);
            }
            
            while (x != z.parent) {
                z = z.getParent();
                z.decreaseSubtreeSize();
            }
        }
        
        /**
         * Deletes node with key "key"
         * @param key - the key to delete
         * @return number of rebalances
         */
        private int delete(int key) {
            NodeDirection direction;
            if (this.key == key)
            {
                this.decreaseSubtreeSize();
                
                if (this.isLeaf()) {
                	// Deleting a leaf
                    if (this.isRoot()) {
                        setRoot(externalNode);
                        return 0;
                    } else {
                        WAVLNode parentNode = this.getParent();
                        parentNode.setChild(this.getParentDirection(), externalNode);
                        return parentNode.deletionBalance();
                    }
                }
                else if (this.getLeft().isExternalNode() || this.getRight().isExternalNode())
                {
                	// Deleting an unary node
                    WAVLNode child = this.getRight().isExternalNode() ? this.getLeft() : this.getRight();
                    if (this.isRoot()) {
                        setRoot(child);
                        child.parent = externalNode;
                        return 0;
                    } else {
                        this.getParent().setChild(this.getParentDirection(), child);
                        return child.getParent().deletionBalance();
                    }
                }
                else
                {
                	// Switch with successor and delete
                    WAVLNode successor = this.successor();
                    WAVLNode successorParent = successor.getParent();
                    this.switchNode(successor);
                    if (this != successorParent) {
                        successorParent.setChild(NodeDirection.Left, this.getRight());
                        successor.updateSubtreeSize();
                        return successorParent.deletionBalance();
                    } else {
                        successor.setChild(NodeDirection.Right, this.getRight());
                        successor.updateSubtreeSize();
                        return successor.deletionBalance();
                    }
                }
            }
            else if (key < this.key)
            {
                direction = NodeDirection.Left;
            }
            else
            {
                direction = NodeDirection.Right;
            }
            
            if (this.getChild(direction).isExternalNode()) {
                // k not found in tree
                WAVLNode lastNode = this;
                while (!lastNode.isRoot()) {
                    lastNode = lastNode.getParent();
                    lastNode.increaseSubtreeSize();
                }
                return -1;
            }
            else
            {
                // find k in tree recursively
                this.decreaseSubtreeSize();
                return this.getChild(direction).delete(key);
            }
            
        }
        
        private int deletionBalance() {
            int rightDifference = this.getRankDifference(NodeDirection.Right);
            int leftDifference = this.getRankDifference(NodeDirection.Left);
            
            if ((leftDifference == 2 && rightDifference == 1) //
                || ((leftDifference == 2 && rightDifference == 2) && (!this.isLeaf())) //
                || (leftDifference == 1 && rightDifference == 2) //
                || (leftDifference == 1 && rightDifference == 1)) {
                // stop recursion if the rank differences are good
                return 0;
            }
            else if (leftDifference == 2 && rightDifference == 2)
            {
            	// slide 52 middle case
            	// leaf with 2,2
                this.demotion();
                return 1 + (this.isRoot() ? 0 : this.getParent().deletionBalance());
            }
            else
            {
            	// one of four cases in slide 54
            	
                if ((leftDifference == 2 && rightDifference == 3) || (leftDifference == 3 && rightDifference == 2)) {
                    // Case 1 slide 55
                    this.demotion();
                    
                    if (this.isRoot()) {
                        return 1;
                    } else {
                        return 1 + this.getParent().deletionBalance();
                    }
                } else {
                    
                    NodeDirection direction    = rightDifference == 1 ? NodeDirection.Right : NodeDirection.Left;
                    NodeDirection oppositeDirection = getOppositeDirection(direction);
                    WAVLNode childNode = this.getChild(direction);
                    int leftChildDifference = childNode.getRankDifference(oppositeDirection);
                    int rightChildDifference = childNode.getRankDifference(direction);
                    
                    if (leftChildDifference == 2 && rightChildDifference == 2) {
                    	// Case 2 Slide 56
                        this.demotion();
                        childNode.demotion();
                        
                        if (this.isRoot()) {
                            return 2;
                        } else {
                            return 2 + this.parent.deletionBalance();
                        }
                        
                    } else if ((leftChildDifference == 1 || leftChildDifference == 2) && rightChildDifference == 1) {
                    	// Case 3 Slide 57
                        this.rotate(oppositeDirection);
                        
                        childNode.promotion();
                        this.demotion();
                        
                        if (this.getRankDifference(oppositeDirection) == 2 && this.getRankDifference(direction) == 2 && this.isLeaf()) {
                            this.demotion();
                        }
                        
                        return 3;
                    } else {
                    	// Case 4 slide 58
                        this.demotion();
                        this.demotion();
                        childNode.demotion();
                        
                        childNode.getChild(oppositeDirection).promotion();
                        childNode.getChild(oppositeDirection).promotion();
                        
                        childNode.rotate(direction);
                        
                        this.rotate(oppositeDirection);
                        
                        return 5;
                    }
                }
            }
        }
        
        /**
         * Returns the direction of parent
         * @return the direction of parent
         */
        private NodeDirection getParentDirection() {
            if (this.getParent().getChild(NodeDirection.Right) == this) {
                return NodeDirection.Right;
            } else {
                return NodeDirection.Left;
            }
        }
        
        /**
         * Returns the opposite direction of "direction"
         * @param direction - current direction
         * @return the opposite direction
         */
        private NodeDirection getOppositeDirection(NodeDirection direction) {
            return direction == NodeDirection.Right ? NodeDirection.Left : NodeDirection.Right;
        }
        
        /**
         * Returns the rank difference between node and one of its children
         * @param direction - the direction of the child
         * @return the rank difference
         */
        public int getRankDifference(NodeDirection direction) {
            return this.rank - this.getChild(direction).rank;
        }
        
        /**
         * Rotates the node in direction "direction"
         * @param direction
         */
        private void rotate(NodeDirection direction) {
            NodeDirection oppositeDirection = getOppositeDirection(direction);
            
            WAVLNode z = this;
            WAVLNode x = z.getChild(oppositeDirection);
            WAVLNode b = x.getChild(direction);
            
            // ensures the parent of x
            if (!z.isRoot()) {
            	z.getParent().setChild(this.getParentDirection(), x);
            } else {
            	setRoot(x);
                x.setParent(null);
            }
            
            z.setChild(oppositeDirection, b);
            x.setChild(direction, z);
            
            z.updateSubtreeSize();
            x.updateSubtreeSize();
            
        }
	}
}
