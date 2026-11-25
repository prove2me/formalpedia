-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.not_mem_sClosure_diff_of_relativeSplitInjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:53:50.469279+00:00
-- url     : https://prove2.me/submissions/e6bc6d36-888f-4ba1-941f-5c933dc7c0a6

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitInjective
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_not_splitMono_of_labels_ne
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
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution
    (C : Set ι) (x : ι)
    (hrel : σ.IsRelativeSplitInjective C x) :
    x ∉ σ.sClosure (C \ {x}) := by
  intro hxgen
  obtain ⟨P⟩ := hxgen
  let P' : σ.SubPresentation C (σ.obj x) :=
    SubPresentation.of_subset σ P Set.sdiff_subset
  have hne : ∀ t, x ≠ P.label t := by
    intro t hEq
    have hnotmem : P.label t ∉ ({x} : Set ι) :=
      (P.mem t).2
    exact hnotmem (by
      simpa only [Set.mem_singleton_iff] using hEq.symm)
  exact (not_splitMono_of_labels_ne σ P hne) (hrel P')
end PretorsionImageClosed.IndecomposableSkeleton
