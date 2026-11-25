-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.qClosure_isAntiExchange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:51:53.163384+00:00
-- url     : https://prove2.me/submissions/a20f3dfe-176e-4a9b-bf6f-caa0b63e3fa4

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_singleton_eq_pointTrace
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_fullyInvariant_linear
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_pointTrace_le_trace_sup_jacobson
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_trace_eq_top
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_insert
public import Theorems.Thm_PretorsionImageClosed_eq_top_of_nilpotent_idealRange
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
theorem _root_.solution
    [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))] :
    σ.qClosure.IsAntiExchange := by
  intro C x y hC hxC _hyC hxy hxgen hygen
  have hxtrace :
      σ.trace C (σ.obj x) ⊔
        σ.pointTrace y (σ.obj x) = ⊤ := by
    have h :=
      (mem_qClosure_iff_trace_eq_top σ (insert y C) x).1 hxgen
    rw [trace_insert, trace_singleton_eq_pointTrace] at h
    exact h
  have hytrace :
      σ.trace C (σ.obj y) ⊔
        σ.pointTrace x (σ.obj y) = ⊤ := by
    have h :=
      (mem_qClosure_iff_trace_eq_top σ (insert x C) y).1 hygen
    rw [trace_insert, trace_singleton_eq_pointTrace] at h
    exact h
  let J := Ring.jacobson (Module.End R (σ.obj x))
  have hsup : σ.trace C (σ.obj x) ⊔
      PretorsionImageClosed.idealRange J = ⊤ := by
    apply top_unique
    rw [← hxtrace]
    exact sup_le le_sup_left
      (pointTrace_le_trace_sup_jacobson σ C hxy hytrace)
  have htraceTop : σ.trace C (σ.obj x) = ⊤ := by
    apply PretorsionImageClosed.eq_top_of_nilpotent_idealRange J
    · exact trace_fullyInvariant_linear σ (σ.obj x)
    · dsimp only [J]
      exact
        (Ideal.jacobson_bot (R :=
          Module.End R (σ.obj x))) ▸
            IsArtinianRing.isNilpotent_jacobson_bot
    · exact hsup
  apply hxC
  rw [← hC.closure_eq]
  exact (mem_qClosure_iff_trace_eq_top σ C x).2 htraceTop
end PretorsionImageClosed.IndecomposableSkeleton
