-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.isLUB_join
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:12:24.785837+00:00
-- url     : https://prove2.me/submissions/3e7ffbec-f1ab-41dd-8b96-e61ef6840add

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_inAdd_mono
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_prop_iff_inAdd_indOf


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
theorem _root_.solution (s : Set {Z : Statement.Subcategory (FGModuleCat.{w} R) // Z.IsImageClosed}) :
    IsLUB s ⟨σ.addOf (σ.iClosure (⋃ Z ∈ s, σ.indOf Z.1)),
      (σ.isImageClosed_addOf_iff _).2 (σ.iClosure.isClosed_closure _)⟩ := by
  refine ⟨fun Z hZ X hX => ?_, fun W hW X hX => ?_⟩
  · rw [σ.prop_iff_inAdd_indOf] at hX
    refine inAdd_mono σ ?_ hX
    exact (subset_biUnion_of_mem (u := fun Z : {Z : Statement.Subcategory (FGModuleCat.{w} R) //
      Z.IsImageClosed} => σ.indOf Z.1) hZ).trans (σ.iClosure.le_closure _)
  · have hle : σ.iClosure (⋃ Z ∈ s, σ.indOf Z.1) ⊆ σ.indOf W.1 := by
      apply ((σ.isImageClosed_iff_isClosed_indOf W.1).1 W.2).closure_le_iff.2
      exact iUnion₂_subset fun Z hZ => σ.indOf_subset_iff.2 (hW hZ)
    rw [σ.prop_iff_inAdd_indOf W.1]
    exact inAdd_mono σ hle hX
end PretorsionImageClosed.IndecomposableSkeleton
