-- Prove2me | solution 1 for OrderConvergesTo.inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:40.576265+00:00
-- url     : https://prove2.me/submissions/68214546-9b0c-4f10-8f57-6d5fe9753838

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
public import Theorems.Thm_OrderConvergesTo_neg
public import Theorems.Thm_OrderConvergesTo_sup

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
    OrderConvergesTo (fun i => u i ⊓ v i) (x ⊓ y) := by
  simpa [neg_sup] using (hu.neg.sup hv.neg).neg
end OrderConvergesTo
