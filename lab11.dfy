// method test1 (x: int , y: int ) returns (z: int )
//  {
//  assume (x==y) ;
//  z:=x-y;
//  assert (z ==0) ;
// }

// //daca x=y, conditie impusa la inceput, iar z este valoarea diferentei acestor 2 numere, atunci z va fi 0

// method test2 (x: int ) returns (z: int )
//  {
//  assume true ;
//  z:=100;
//  assert (z ==100) ;
// }

// //daca initializam z cu 100, atunci valoarea returnata va fi 100

// method test3 (x: int ) returns (z: int )
//  {
//  assume 0 <= x < 100 ;
// z:=x+1;
//  assert (0 <= x <= 100) ;
// }

// //daca x ia valori de la 0 la 99, si x creste +1, atunci x va fi in final de la 0 la 100


// method test4 (y: int ) returns (x: int )
//  {
//  assume true ;
//  x:=2*y;
//  assert (y<=x) ;
// }
// //daca y este negativ, sa presupunem -1, z devine -2, care este este mai mic decat -1, deci assertul se infirma







method sum (n: int) returns (sum: int)
requires n>=0
ensures sum==n*(n+1)/2
{
    sum:=0;
    var i := 1;
    while(i<=n)
    invariant i>=0;
    invariant i<=n+1;
    invariant sum==i*(i-1)/2;
    {
        sum:=sum+i;
        i:=i+1
    }

}