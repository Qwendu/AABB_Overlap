datatype AABB = AABB(min_x : int, min_y : int, max_x : int, max_y : int)
datatype InOut = In(idx : int) | Out(idx : int)

predicate before(f : InOut, s : InOut)
{
	f.idx == s.idx ==> In(f.idx) == f && Out(f.idx) == s
}

function overlaps_x (a : AABB, b : AABB) : bool
{
	!(a.max_x < b.min_x || b.max_x < a.min_x)
}
function overlaps_y (a : AABB, b : AABB) : bool
{
	!(a.max_y < b.min_y || b.max_y < a.min_y)
}

function overlaps (a : AABB, b : AABB) : bool
{
	overlaps_x(a,b) && overlaps_y(a,b)
}

predicate in_before_out(li : seq<InOut>, k : int)
{
	forall i :: 0 <= i < |li| ==> In(k) in li[i..] && In(k) !in li[i + 1..] ==> Out(k) in li[i + 1..]
}

method order_by_x (li : seq<AABB>) returns (order : seq<InOut>)
	ensures forall i :: 0 <= i < |li| ==> In(i) in order && Out(i) in order
	ensures forall i :: 0 <= i < |order| ==> 0 <= order[i].idx < |li|
	ensures |order| == |li| + |li|
	ensures |order| % 2 == 0
	ensures forall i :: 0 <= i < |li| ==> in_before_out(order, i)
	ensures |multiset(order)| == |order|
{
	order := [];
	for i := 0 to |li|
		invariant forall j :: 0 <= j < i ==> In(j) in order && Out(j) in order
		invariant forall j :: 0 <= j < |order| ==> 0 <= order[j].idx < |li|
		invariant |order| == i + i
		invariant 0 <= i <= |li|
		invariant |order| % 2 == 0
		invariant forall j :: 0 <= j < i ==> in_before_out(order, j)
	{
		assert 0 <= i < |li|;
		assert forall m :: 0 <= m < i ==> In(m)  in order;
		assert forall m :: 0 <= m < i ==> Out(m) in order;


		var in_idx  : int := |order| / 2;
		var out_idx : int := |order|;

		ghost var old_order : seq<InOut> := order;
		assert forall j :: 0 <= j < i ==> in_before_out(order, j);
		order := 
		    order[..in_idx] 
		  + [In(i)] 
		  + order[in_idx..out_idx] 
		  + [Out(i)] 
		  + order[out_idx..];
		assert forall j :: 0 <= j <= i ==> in_before_out(order, j);
		

		


		assert In(i)  == order[ in_idx];
		assert Out(i) == order[out_idx + 1];
		assert exists j,k :: 0 <= j < k < |order| && before(order[j], order[k]);
		assert exists j,k :: 0 <= j < k < |order| && In(i) == order[j] && Out(i) == order[k];
		assert exists j :: 0 <= j < |order| && In(i)  == order[j];
		assert exists k :: 0 <= k < |order| && Out(i) == order[k];
		assert exists j,k :: 0 <= j < k < |order| && In(i) == order[j] && Out(i) == order[k];

		assert exists j,k :: 0 <= j < k < |order| && before(order[j], order[k]);

		
	}
}

method split_along_x(li : seq<AABB>) returns (split : bool, f : seq<AABB>, s : seq<AABB>)
	//ensures |li| == |f| + |s|
	//ensures forall x :: x in f ==> x !in s
	//ensures forall x :: x in s ==> x !in f
{
	split := false;
	f := li;
	s := [];
	if |li| == 1
	{
		return;
	}else{
		var order : seq<InOut> := order_by_x(li);
		assert |order| == |li| + |li|;
		
		var in_count    : int := 0;
		var out_count : int := 0;
		var split_idx : int := 0;
		for i := 0 to |order|
			invariant 0 <= i <= |order|
			//invariant forall x :: Out(x) in order[..i] ==> In(x) in order[..i]
			//invariant in_count >= out_count
		{
			match order[i]
			{
				case In(i)  =>  in_count :=  in_count + 1;
				case Out(i) => out_count := out_count + 1;
			}
			if in_count == out_count
			{
				split_idx := i + 1;
				break;
			}
		}
		split := split_idx != |order|;
		assert 0 <= split_idx <= |order|;
		//assert split_idx % 2 == 0;

		var first_order  : seq<InOut> := order[..split_idx];
		//assert forall x :: In(x) in first_order ==> Out(x) in first_order;

		var second_order : seq<InOut> := order[split_idx..];

		//assert forall i :: In(i) in first_order ==> Out(i) in first_order;
		ghost var total : int := 0;
		f := [];
		for i := 0 to |first_order|
			invariant total == |f|
		{

			match first_order[i]
			case In(idx) => 
			{
				f := f + [li[idx]];
				total := total + 1;
			}
			case Out(_)  => {}
		}
		s := [];
		for i := 0 to |second_order|
			invariant total == |f| + |s|
		{
			match second_order[i]
			case In(idx) =>
			{
				s := s + [li[idx]];
				total := total + 1;
			}
			case Out(_)  => {}
		}
		assert total == |f| + |s|;
		//assert total == |li|;
		return;
	}
}

method count_overlaps (li : seq<seq<AABB>>) returns (over : int)
{
	over := 0;
	for c := 0 to |li|
	{
		var cluster : seq<AABB> := li[c];
		for i := 0 to |cluster|
		{
			for j := i to |cluster|
			{
				if overlaps(cluster[i], cluster[j])
				{
					over := over + 1;
				}
			}
		}
	}
}

method partition_AABBs(li : seq<AABB>) returns (clusters : seq<seq<AABB>>)
	decreases *
{
	clusters := [li];
	if |li| < 1
	{
		return;
	}
	assert 0 <= |li| - |clusters|;

	while true
		//invariant |clusters| <= |li| 
		//decreases |li| - |clusters|
		decreases *
	{
		ghost var before : seq<seq<AABB>> := clusters;
		var added : int := 0;

		for c := 0 to |clusters|
			//invariant |clusters| <= |li| 
			invariant 0 <= c <= |clusters|
			invariant |clusters| >= |before|
			invariant |before| + added == |clusters|
		{
			var split : bool, f : seq<AABB>, s : seq<AABB> := split_along_x(clusters[c]);
			//assert |f| + |s| == |clusters[c]|;
			
			if split
			{
				clusters := clusters[c := f] + [s];
				added := added + 1;
			}
		}
		assert |before| + added == |clusters|;
		if added == 0
		{
			break;
		}
		print_clusters(clusters);
		assert |clusters| > |before|;
	}
}

method Main ()
	decreases *
{
	var li : seq<AABB> := [AABB(0,0,1,1), AABB(2,2,3,3), AABB(4,4,5,5)];
	print_aabbs(li);

	var clusters : seq<seq<AABB>> := partition_AABBs(li);
	print_clusters(clusters);
	
}

method print_clusters (li : seq<seq<AABB>>)
{
	for i := 0 to |li|
	{
		print i, ":\n";
		print_aabbs(li[i]);
	}
}

method print_aabbs (li : seq<AABB>)
{
	for i := 0 to |li|
	{
		print li[i], "\n";
	}
}


