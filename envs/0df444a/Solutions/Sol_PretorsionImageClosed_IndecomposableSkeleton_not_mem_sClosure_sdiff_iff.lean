-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.not_mem_sClosure_sdiff_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:13:23.492397+00:00
-- url     : https://prove2.me/submissions/ac606cb5-d9b2-43e2-bd33-0aa0c60c98c4

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_isRelativeSplitInjective_iff
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_not_mem_sClosure_diff_iff_relativeSplitInjective


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
theorem _root_.solution (Z : Statement.Subcategory (FGModuleCat.{w} R)) (x : ι) :
    x ∉ σ.sClosure (σ.indOf Z \ {x}) ↔ IsSplittingInjective Z (σ.obj x) :=
  (σ.not_mem_sClosure_diff_iff_relativeSplitInjective _ x).trans
    (σ.isRelativeSplitInjective_iff Z x)
end PretorsionImageClosed.IndecomposableSkeleton
