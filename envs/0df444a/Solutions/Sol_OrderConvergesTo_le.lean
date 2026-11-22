-- Prove2me | solution 1 for OrderConvergesTo.le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:18.6798+00:00
-- url     : https://prove2.me/submissions/d9408ae3-02cd-4090-b102-f2e8a0d25bdd

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
public import Theorems.Thm_OrderConvergesTo_nonneg
public import Theorems.Thm_OrderConvergesTo_sub

set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open OrderConvergesTo
namespace OrderConvergesTo
theorem _root_.solution {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u v : ι → X} {x y : X} (hu : OrderConvergesTo u x)
    (hv : OrderConvergesTo v y) (hle : ∀ i, u i ≤ v i) :
    x ≤ y := by
  have hsub : OrderConvergesTo (fun i => v i - u i) (y - x) := hv.sub hu
  exact sub_nonneg.mp (hsub.nonneg fun i => sub_nonneg.mpr (hle i))
end OrderConvergesTo
