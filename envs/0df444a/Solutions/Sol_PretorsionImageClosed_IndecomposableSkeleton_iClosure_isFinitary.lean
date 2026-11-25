-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.iClosure_isFinitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T07:12:16.987161+00:00
-- url     : https://prove2.me/submissions/01549345-0ab6-474a-af70-8ffcd7e07cb7

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_finite_witness
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_finite_witness


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
theorem _root_.solution : σ.iClosure.IsFinitary := by
  intro S j hj
  obtain ⟨T₁, hT₁, hT₁S, h₁⟩ := qSet_finite_witness σ hj.1
  obtain ⟨T₂, hT₂, hT₂S, h₂⟩ := sSet_finite_witness σ hj.2
  exact ⟨T₁ ∪ T₂, hT₁.union hT₂, union_subset hT₁S hT₂S,
    qSet_monotone σ subset_union_left h₁, sSet_monotone σ subset_union_right h₂⟩
end PretorsionImageClosed.IndecomposableSkeleton
