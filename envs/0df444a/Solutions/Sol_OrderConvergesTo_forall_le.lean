-- Prove2me | solution 1 for OrderConvergesTo.forall_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:13.923075+00:00
-- url     : https://prove2.me/submissions/601aa427-1bea-4249-b6a2-319dc482bc24

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
public import Theorems.Thm_orderConvergesTo_const
public import Theorems.Thm_OrderConvergesTo_le

set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open OrderConvergesTo
namespace OrderConvergesTo
theorem _root_.solution {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u : ι → X} {a x : X} (hu : OrderConvergesTo u x) (hau : ∀ i, a ≤ u i) :
    a ≤ x :=
  (orderConvergesTo_const a).le hu hau
end OrderConvergesTo
