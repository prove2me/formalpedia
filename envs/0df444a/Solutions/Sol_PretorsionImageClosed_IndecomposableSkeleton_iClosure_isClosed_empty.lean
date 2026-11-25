-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.iClosure_isClosed_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T07:08:57.393806+00:00
-- url     : https://prove2.me/submissions/3c9fc361-4123-44ff-b0ec-5b0ce2f192a7

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.qSet_empty



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
theorem _root_.solution : σ.iClosure.IsClosed ∅ := by
  rw [ClosureOperator.isClosed_iff]
  show σ.qSet ∅ ∩ σ.sSet ∅ = ∅
  rw [qSet_empty, empty_inter]
end PretorsionImageClosed.IndecomposableSkeleton
