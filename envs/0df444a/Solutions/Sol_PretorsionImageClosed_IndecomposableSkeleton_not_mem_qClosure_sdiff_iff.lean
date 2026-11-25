-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.not_mem_qClosure_sdiff_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T07:30:33.403283+00:00
-- url     : https://prove2.me/submissions/04d56311-c253-41cb-ba22-cf5089ea2c76

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_isRelativeSplitProjective_iff
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_not_mem_qClosure_sdiff_iff_isRelativeSplitProjective


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
    x ∉ σ.qClosure (σ.indOf Z \ {x}) ↔ IsSplittingProjective Z (σ.obj x) :=
  (σ.not_mem_qClosure_sdiff_iff_isRelativeSplitProjective _ x).trans
    (σ.isRelativeSplitProjective_iff Z x)
end PretorsionImageClosed.IndecomposableSkeleton
