-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.sClosure_isFinitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:56:56.006861+00:00
-- url     : https://prove2.me/submissions/47dbde19-d44e-4675-b18b-ab251393aea7

module
public import Mathlib.CategoryTheory.FintypeCat
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Skeleton
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_finite_witness

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution : σ.sClosure.IsFinitary := by
  intro S j hj
  exact sSet_finite_witness σ hj
end PretorsionImageClosed.IndecomposableSkeleton
