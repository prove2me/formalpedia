-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.exists_sdiff_eq_singleton_of_covby
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T07:29:12.216978+00:00
-- url     : https://prove2.me/submissions/b91df392-17a7-45b3-9e49-27df4beff0fb

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_iClosure_isAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_indOf_addOf
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qClosure_isAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sClosure_isAntiExchange


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
    (h : Z' ⋖ Z) : ∃ x, σ.indOf Z.1 \ σ.indOf Z'.1 = {x} := by
  have hlt : σ.indOf Z'.1 ⊂ σ.indOf Z.1 := by
    have := (σ.imageClosedOrderIso).lt_iff_lt.2 h.lt
    exact this
  obtain ⟨x, hxZ, hxZ'⟩ := exists_of_ssubset hlt
  have hC : σ.iClosure.IsClosed (σ.indOf Z'.1) :=
    (σ.isImageClosed_iff_isClosed_indOf Z'.1).1 Z'.2
  have hD : σ.iClosure.IsClosed (σ.indOf Z.1) :=
    (σ.isImageClosed_iff_isClosed_indOf Z.1).1 Z.2
  -- adjoining any new representative recovers `Z`
  have hfill : ∀ y ∈ σ.indOf Z.1 \ σ.indOf Z'.1,
      σ.iClosure (insert y (σ.indOf Z'.1)) = σ.indOf Z.1 := by
    rintro y ⟨hyZ, hyZ'⟩
    let W : {Z : Statement.Subcategory (FGModuleCat.{w} R) // Z.IsImageClosed} :=
      (σ.imageClosedOrderIso).symm ⟨σ.iClosure (insert y (σ.indOf Z'.1)), σ.iClosure.isClosed_closure _⟩
    have hW : σ.indOf W.1 = σ.iClosure (insert y (σ.indOf Z'.1)) := σ.indOf_addOf _
    have hle : W ≤ Z := by
      rw [← (σ.imageClosedOrderIso).le_iff_le]
      show σ.indOf W.1 ⊆ σ.indOf Z.1
      rw [hW]
      exact hD.closure_le_iff.2 (insert_subset hyZ hlt.subset)
    have hge : Z' < W := by
      rw [← (σ.imageClosedOrderIso).lt_iff_lt]
      show σ.indOf Z'.1 ⊂ σ.indOf W.1
      rw [hW]
      refine ssubset_of_subset_of_ne ((subset_insert _ _).trans (σ.iClosure.le_closure _)) ?_
      intro heq
      apply hyZ'
      rw [heq]
      exact σ.iClosure.le_closure _ (mem_insert _ _)
    have hWZ : W = Z := by
      by_contra hne
      exact h.2 hge (lt_of_le_of_ne hle hne)
    rw [← hW, hWZ]
  refine ⟨x, ?_⟩
  apply Subset.antisymm
  · intro y hy
    by_contra hyx
    have hae := σ.iClosure_isAntiExchange (σ.qClosure_isAntiExchange) (σ.sClosure_isAntiExchange)
    refine hae hC hy.2 hxZ' (fun hyx' => hyx (mem_singleton_iff.2 hyx')) ?_ ?_
    · rw [hfill x ⟨hxZ, hxZ'⟩]
      exact hy.1
    · rw [hfill y hy]
      exact hxZ
  · rintro y rfl
    exact ⟨hxZ, hxZ'⟩
end PretorsionImageClosed.IndecomposableSkeleton
