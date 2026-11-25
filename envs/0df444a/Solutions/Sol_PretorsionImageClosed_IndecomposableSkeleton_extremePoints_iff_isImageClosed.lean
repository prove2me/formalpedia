-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.extremePoints_iff_isImageClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T07:46:39.904052+00:00
-- url     : https://prove2.me/submissions/4cafb011-deef-4cba-a379-01f09a779030

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Theorems.Thm_PretorsionImageClosed_SetClosure_mem_extremePoints_iff_isClosed_sdiff_singleton


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
omit [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))]
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution {Z : Statement.Subcategory (FGModuleCat.{w} R)}
    (hZ : Z.IsImageClosed) {x : ι} (hx : x ∈ σ.indOf Z) :
    x ∈ σ.iClosure.extremePoints (σ.indOf Z) ↔ (σ.addOf (σ.indOf Z \ {x})).IsImageClosed := by
  rw [SetClosure.mem_extremePoints_iff_isClosed_sdiff_singleton
    ((σ.isImageClosed_iff_isClosed_indOf Z).1 hZ) hx, isImageClosed_addOf_iff]
end PretorsionImageClosed.IndecomposableSkeleton
