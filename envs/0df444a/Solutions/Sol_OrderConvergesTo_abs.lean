-- Prove2me | solution 1 for OrderConvergesTo.abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:39.291003+00:00
-- url     : https://prove2.me/submissions/f48df150-fddf-45fe-af38-b4433e1f7e37

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
    {u : ι → X} {x : X} (hu : OrderConvergesTo u x) :
    OrderConvergesTo (fun i => |u i|) |x| := by
  change OrderConvergesTo (fun i => u i ⊔ -u i) (x ⊔ -x)
  exact hu.sup hu.neg
end OrderConvergesTo
