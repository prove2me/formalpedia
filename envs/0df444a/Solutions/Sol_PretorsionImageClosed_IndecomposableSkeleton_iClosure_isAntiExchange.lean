-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.iClosure_isAntiExchange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T07:11:33.712368+00:00
-- url     : https://prove2.me/submissions/970d93ab-41d6-4a5a-9b38-12b5f73499a2

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R] {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution (hq : σ.qClosure.IsAntiExchange)
    (hs : σ.sClosure.IsAntiExchange) : σ.iClosure.IsAntiExchange := by
  intro C x y hC hxC hyC hxy hx hy
  have hCeq : σ.qSet C ∩ σ.sSet C = C := hC.closure_eq
  -- one of the two closures already excludes `x`
  have key : ∀ (c : SetClosure ι), c.IsAntiExchange → x ∉ c C →
      x ∈ c (insert y C) → y ∈ c (insert x C) → False := by
    intro c hc hxc hxy' hyx'
    by_cases hyc : y ∈ c C
    · apply hxc
      have : insert y C ⊆ c C := insert_subset hyc (c.le_closure C)
      exact ((c.monotone this).trans (c.idempotent C).le) hxy'
    · refine hc (c.isClosed_closure C) hxc hyc hxy ?_ ?_
      · exact c.monotone (insert_subset_insert (c.le_closure C)) hxy'
      · exact c.monotone (insert_subset_insert (c.le_closure C)) hyx'
  have hx' : x ∉ σ.qSet C ∩ σ.sSet C := by rw [hCeq]; exact hxC
  rcases not_and_or.1 hx' with hxq | hxs
  · exact key σ.qClosure hq hxq hx.1 hy.1
  · exact key σ.sClosure hs hxs hx.2 hy.2
end PretorsionImageClosed.IndecomposableSkeleton
