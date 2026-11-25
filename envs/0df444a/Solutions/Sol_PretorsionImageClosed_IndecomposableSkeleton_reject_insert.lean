-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.reject_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:53:25.956662+00:00
-- url     : https://prove2.me/submissions/a9750155-68c5-4ad5-a557-7840730611a6

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_singleton_eq_pointReject
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_union
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
public import Theorems.Thm_PretorsionImageClosed_idealKernel_bot
public import Theorems.Thm_PretorsionImageClosed_idealKernel_top
public import Theorems.Thm_PretorsionImageClosed_idealRange_bot
public import Theorems.Thm_PretorsionImageClosed_idealRange_top
public import Theorems.Thm_PretorsionImageClosed_mem_endNonunitsIdeal_iff
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.mem_qClosure_iff_inFac
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.mem_sClosure_iff_inSub
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.qSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.reject_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.sSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.trace_empty
attribute [local simp] PretorsionImageClosed.idealKernel_bot
attribute [local simp] PretorsionImageClosed.idealKernel_top
attribute [local simp] PretorsionImageClosed.idealRange_bot
attribute [local simp] PretorsionImageClosed.idealRange_top
attribute [local simp] PretorsionImageClosed.mem_endNonunitsIdeal_iff



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
theorem _root_.solution (S : Set ι) (i : ι)
    (X : FGModuleCat.{w} R) :
    σ.reject (insert i S) X =
      σ.reject S X ⊓ σ.pointReject i X := by
  rw [show insert i S = S ∪ {i} by ext; simp]
  rw [reject_union, reject_singleton_eq_pointReject]
end PretorsionImageClosed.IndecomposableSkeleton
