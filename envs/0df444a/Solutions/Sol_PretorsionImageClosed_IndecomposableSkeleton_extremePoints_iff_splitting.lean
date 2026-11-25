-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.extremePoints_iff_splitting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:49:46.219892+00:00
-- url     : https://prove2.me/submissions/293ab084-3d9c-4e3e-8917-af5322e5f93e

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_iClosure_apply
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_not_mem_qClosure_sdiff_iff
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_not_mem_sClosure_sdiff_iff
public import Theorems.Thm_PretorsionImageClosed_SetClosure_mem_extremePoints


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
variable [IsArtinianRing R]
variable [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))]
omit [IsArtinianRing R]
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution {Z : Statement.Subcategory (FGModuleCat.{w} R)} {x : ι}
    (hx : x ∈ σ.indOf Z) :
    x ∈ σ.iClosure.extremePoints (σ.indOf Z) ↔
      IsSplittingProjective Z (σ.obj x) ∨ IsSplittingInjective Z (σ.obj x) := by
  rw [SetClosure.mem_extremePoints, and_iff_right hx, iClosure_apply, mem_inter_iff, not_and_or,
    σ.not_mem_qClosure_sdiff_iff, σ.not_mem_sClosure_sdiff_iff]
end PretorsionImageClosed.IndecomposableSkeleton
