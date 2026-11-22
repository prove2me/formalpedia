-- Prove2me | solution 1 for OrderConvergesTo.sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:39.926909+00:00
-- url     : https://prove2.me/submissions/037bc9e1-c306-470a-b696-c449a611ffe9

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
public import Theorems.Thm_OrderConvergesTo_add
public import Theorems.Thm_OrderConvergesTo_neg

set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open OrderConvergesTo
namespace OrderConvergesTo
theorem _root_.solution {ι : Type v} [Preorder ι]
    {u v : ι → X} {x y : X} (hu : OrderConvergesTo u x)
    (hv : OrderConvergesTo v y) :
    OrderConvergesTo (fun i => u i - v i) (x - y) := by
  simpa [sub_eq_add_neg] using hu.add hv.neg
end OrderConvergesTo
