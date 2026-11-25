-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.sClosure_isAntiExchange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:54:12.531007+00:00
-- url     : https://prove2.me/submissions/f8bae5c8-7646-49c7-a4fa-831c8caf4c8a

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_insert
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_fullyInvariant_linear
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_inf_idealKernel_eq_bot
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_reject_eq_bot
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
public import Theorems.Thm_PretorsionImageClosed_eq_bot_of_inf_idealKernel
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
    σ.sClosure.IsAntiExchange := by
  intro C x y hC hxC _hyC hxy hxgen hygen
  have hxreject :
      σ.reject C (σ.obj x) ⊓
        σ.pointReject y (σ.obj x) = ⊥ := by
    have h :=
      (mem_sClosure_iff_reject_eq_bot σ (insert y C) x).1 hxgen
    rw [reject_insert] at h
    exact h
  have hyreject :
      σ.reject C (σ.obj y) ⊓
        σ.pointReject x (σ.obj y) = ⊥ := by
    have h :=
      (mem_sClosure_iff_reject_eq_bot σ (insert x C) y).1 hygen
    rw [reject_insert] at h
    exact h
  let J := Ring.jacobson (Module.End R (σ.obj x))
  have hinf :
      σ.reject C (σ.obj x) ⊓
        PretorsionImageClosed.idealKernel J = ⊥ :=
    reject_inf_idealKernel_eq_bot σ C hxy hxreject hyreject
  have hrejectBot : σ.reject C (σ.obj x) = ⊥ := by
    apply PretorsionImageClosed.eq_bot_of_inf_idealKernel J
    · exact reject_fullyInvariant_linear σ (σ.obj x)
    · dsimp only [J]
      exact
        (Ideal.jacobson_bot (R :=
          Module.End R (σ.obj x))) ▸
            IsArtinianRing.isNilpotent_jacobson_bot
    · exact hinf
  apply hxC
  rw [← hC.closure_eq]
  exact (mem_sClosure_iff_reject_eq_bot σ C x).2 hrejectBot
end PretorsionImageClosed.IndecomposableSkeleton
