-- Prove2me | solution 1 for OrderConvergesTo.le_of_forall_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:33.339806+00:00
-- url     : https://prove2.me/submissions/e683c1b8-3c3a-4fa0-ba2d-f94a4d30527c

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
    {u : ι → X} {x b : X} (hu : OrderConvergesTo u x) (hub : ∀ i, u i ≤ b) :
    x ≤ b :=
  hu.le (orderConvergesTo_const b) hub
end OrderConvergesTo
