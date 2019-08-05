 lemma DividesFactor(n : nat, k : int)
  requires n != 0
  ensures (k*n) / n == k
  ensures (k*n) % n == 0
{

  //calculate a temparay var res
  var res := (k*n)/n;

  // use the division rule: b = a*(b/a) + b%a
  assert k*n == res * n + (k*n) % n;
  //the remainder term must be between 0 an n
  assert 0 <= (k*n) % n < n;

  //The number must be greater than qoutient
  assert k*n >= res * n;
  //The number must be less than worst case value of remainder
  assert k*n < res * n + n;

  // from k*n>=res*n
  assert k >= res;

  // rearrange the above equation
  assert k*n - res*n - n < 0;

  //take n common
  assert (k - res - 1) * n < 0;


  var res2 := k - res - 1;

  assert res2 <= 0 ==> res2 * n <= 0;

  assert res2 < 0;
  //can be directly implied from (k-res-1)*n , but we need to assist dafny with this too!!
  assert k - res - 1 < 0;

  //finally we show that res like between k-1 and k and it greater than k-1. So, it must be equal to k. 
  assert k - 1 < res <= k;
}


lemma ModuloRule(n : int, m : nat, k : int)
  requires m != 0
  ensures (n + k * m) % m == n % m
{
  // same rule as the previous section, splitting the number into quotient and remainder
  assert n+k*m == (n+k*m)/m * m + (n+k*m)%m;

  assert n == n/m*m + n%m;

  assert n/m*m + n%m + k*m == (n+k*m)/m * m + (n+k*m)%m;

  assert n/m*m + k*m - (n+k*m)/m * m == (n+k*m)%m - n%m;

  assert (n/m + k - (n+k*m)/m) * m == (n+k*m)%m - n%m;

  var res := n/m + k - (n+k*m)/m;

  DividesFactor(m, res);

  assert -1 < res < 1;

}

//
lemma AdditionMod(a : int, b : int, k : nat)
  requires k != 0
  requires a % k == 0
  requires b % k == 0

  ensures (a + b) % k == 0
  ensures (a - b) % k == 0
{
    assert a == (a / k) * k;
    assert b == (b / k) * k;

    assert a + b == (a/k + b/k) * k;
    assert a - b == (a/k - b/k) * k;

    DividesFactor(k, a/k + b/k);
    DividesFactor(k, a/k - b/k);
}

lemma AddMod(a : int, b : int, k : nat)
  requires k != 0

  ensures (a + b) % k == (a % k + b % k) % k
  ensures (a - b) % k == (a % k - b % k) % k
{

    ModuloRule(a % k + b % k, k, a/k + b/k);
    ModuloRule(a % k - b % k, k, a/k - b/k);
}



predicate div(x : nat, y : nat) {
  x != 0 && y % x == 0
}

//ref: https://github.com/ningit/vaed
function gcd(x : nat, y : nat) : nat
  requires x != 0 || y != 0
{
  if x == 0   then  y
  else if y == 0  then  x
  else if x > y   then  gcd(y, x % y)
      else  gcd(x, y % x)
}

predicate xgcd(x : nat, y : nat, m : nat)
  requires x != 0 || y != 0
{
  div(m, x) && div(m, y)
  && forall d : nat | div(d, x) && div(d, y) :: div(d, m)
}


lemma div_lem(x : nat, y : nat)
  requires y > 0
  ensures forall d : nat | div(d, y) :: x % d == (x % y) % d
{
  
  assert x == (x/y) * y + x % y;
  forall d : nat | div(d, y)
    ensures x % d == (x % y) % d
  {
    assert y == (y/d) * d;
    var f := (x/y) * (y/d);
    assert x == f * d + x % y;
    ModMasMultiplo(x % y, d, f);
    assert x % d == (x % y) % d;
  }
}

lemma f_gcd(x : nat, y : nat)
  requires x != 0 || y != 0
  ensures  xgcd(x, y, gcd(x, y))
  decreases y, x
{
  if x < y {
    f_gcd(y, x);
  }
  else {
    if y == 0 {     
      assert gcd(x, 0) == x;
      assert div(x, 0);
    }
    else {
      f_gcd(y, x % y);
      assert xgcd(y, x % y, gcd(x, y));
      div_lem(x, y);
    }
  }
}

method iter_gcd(x0 : nat, y0 : nat) returns (x : nat)
  requires x0 > y0 >= 0
  ensures x == gcd(x0, y0)
{
  var y;

  x, y := x0, y0;

  while y != 0
    invariant 0 <= y < x
    invariant gcd(x, y) == gcd(x0, y0)
  {
    x, y := y, x % y;
  }
}
  module FieldElement{
      const p : nat := 115792089237316195423570985008687907853269984665640564039457584007908834671663;
    
    function method add(a : nat, b: nat) :nat
    requires a >=0 && b >= 0
    {
      (a + b) % p
    }
    
    function method mul(a: nat, b: nat): nat
    requires a>=0 && b>=0
    {
      (a*b)%p
    }
  
  method PowerMod(A:int, B:nat, P: nat) returns (z:int) 
   // requires A >= 0
   requires B >= 0
   requires P > 0
  //  ensures z == power(A,B)
  {
   var x := A;
   var y := B;
   z := 1;
   
   while y != 0 
  //    invariant power(A, B) == z * power(x, y)
   {
  //    halfExponentSquareBase(x, if odd(y) then y-1 else y);
     
     if y % 2 == 1
     {
       y := y - 1;
       z := (z * x)%P;
     }
     y := y/2;
     x := (x * x)%P;
   }
  }
  
    
  method Power(A:int, B:int) returns (z:int) 
   requires A > 0
   requires B >= 0
   ensures z == power(A,B)
  {
   var x := A;
   var y := B;
   z := 1;
   
   while y != 0
     invariant x > 0
     invariant y >= 0
     invariant power(A, B) == z * power(x, y)
   {
     halfExponentSquareBase(x, if odd(y) then y-1 else y);
     
     if odd(y)
     {
       y := y - 1;
       z := z * x;
     }
     y := y/2;
     x := x * x;
   }
  }
  
  lemma halfExponentSquareBase(x:int,y:int)
   requires x > 0
   requires y >= 0
   requires even(y)
   ensures power(x, y) == power(x*x, y/2)
  {
    if y != 0 {
      halfExponentSquareBase(x,y-2);
    }
  }
  
  predicate method even(n: nat)
    ensures even(n) <==> n % 2 == 0
  {
    if n == 0 then true else odd(n-1)
  }
  
  predicate method odd(n: nat)
    ensures odd(n) <==> n % 2 != 0
  {
    if n == 0 then false else even(n-1)
  }
  
  function power(x:int, n:int):int
  {
   if n <= 0 then 1
   else x * power(x, n-1)
  }
  }
  
  module ecc{
    
      import F = FieldElement
      const secp_b : nat := 7
      const gx : nat := 55066263022277343669578718895168534326250603453777594175500187360389116729240;
      const gy : nat := 32670510020758816978083085130507043184471273380659243275938904335757337482424;
      
      class Point{
        var x: nat;
        var y: nat;
      
      predicate valid()
      reads this
      {

          (x*x*x + 7)%F.p == (y*y)%F.p && 0 < x < F.p && 0 < y < F.p
          // F.add(F.mul(F.mul(x,x), x), secp_b) == F.mul(y,y)
      }
      method Init(x1: nat, y1: nat)
      modifies this
      requires x >=0
      requires y >=0 
      {
        x := x1 % F.p;
        y := y1 % F.p;
      }
      
      }
      
     method add(a : Point, b: Point) returns (c: Point)
     requires a.valid()
     requires b.valid()
     requires a.x != b.x  
     {
       if a.x != b.x
          {
             var a_b := a.x - b.x;
             if a_b <= 0 {a_b := -1 * a_b;}
             if a_b > F.p {a_b := a_b - F.p;}
             assert a_b > 0 && a_b < F.p; 
             var inv := F.PowerMod(a_b, F.p-1, F.p);
             var m := (a.y − b.y)*inv;           
          }
      c := new Point;
      c.Init(1,1);
     }
      method Test()
      {
        var G := new Point;
        G.Init(gx,gy);
        // assert  F.add(F.mul(F.mul(gx,gx), gx), 7) == F.mul(gy,gy);
       assert (gx*gx*gx + 7) %F.p == (gy*gy)%F.p;
  //      assert G.valid();
      }   
  //    method add(Point a, Point b) returns (Point C)
  //    {
  //        
  //    }
  }
  
  method Test() 
  {  
      var p : nat := 115792089237316195423570985008687907853269984665640564039457584007908834671663;
      var x : nat := 123;
      var z: nat := FieldElement.mul(x,x);
      assert z == (x*x)%p;
  //  assert ((x*x*x + 7) %p) == (y*y % p);
  }
  
