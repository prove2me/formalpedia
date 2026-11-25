-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.ncard_of_covby
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T07:52:31.589695+00:00
-- url     : https://prove2.me/submissions/f9fd5ec7-aed0-48d4-8443-575f56603b51

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_exists_sdiff_eq_singleton_of_covby

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
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution
    {Z Z' : {Z : Statement.Subcategory (FGModuleCat.{w} R) // Z.IsImageClosed}}
    (h : Z' ⋖ Z) (hfin : (σ.indOf Z.1).Finite) :
    (σ.indOf Z.1).ncard = (σ.indOf Z'.1).ncard + 1 := by
  obtain ⟨x, hx⟩ := σ.exists_sdiff_eq_singleton_of_covby h
  have hsub : σ.indOf Z'.1 ⊆ σ.indOf Z.1 := σ.indOf_subset_iff.2 h.le
  have hxZ' : x ∉ σ.indOf Z'.1 := by
    have : x ∈ σ.indOf Z.1 \ σ.indOf Z'.1 := by rw [hx]; exact mem_singleton x
    exact this.2
  have heq : σ.indOf Z.1 = insert x (σ.indOf Z'.1) := by
    rw [← union_sdiff_cancel hsub, hx, union_singleton]
  rw [heq, ncard_insert_of_notMem hxZ' (hfin.subset hsub)]
end PretorsionImageClosed.IndecomposableSkeleton
