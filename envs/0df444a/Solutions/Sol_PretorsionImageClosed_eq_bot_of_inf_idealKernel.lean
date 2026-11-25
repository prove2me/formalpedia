-- Prove2me | solution 1 for PretorsionImageClosed.eq_bot_of_inf_idealKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:42:36.182507+00:00
-- url     : https://prove2.me/submissions/f5e5de93-6ade-4793-89cf-afaacce4697d

module
public import Mathlib.RingTheory.Artinian.Ring
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Theorems.Thm_PretorsionImageClosed_mem_endNonunitsIdeal_iff
public import Theorems.Thm_PretorsionImageClosed_idealRange_bot
public import Theorems.Thm_PretorsionImageClosed_idealRange_top
public import Theorems.Thm_PretorsionImageClosed_idealKernel_le_ker
public import Theorems.Thm_PretorsionImageClosed_idealKernel_bot
public import Theorems.Thm_PretorsionImageClosed_idealKernel_top
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.mem_qClosure_iff_inFac
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.mem_sClosure_iff_inSub
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.qSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.reject_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.sSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.trace_empty


attribute [local simp] PretorsionImageClosed.mem_endNonunitsIdeal_iff
attribute [local simp] PretorsionImageClosed.idealRange_bot
attribute [local simp] PretorsionImageClosed.idealRange_top
attribute [local simp] PretorsionImageClosed.idealKernel_bot
attribute [local simp] PretorsionImageClosed.idealKernel_top

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Function
open PretorsionImageClosed
universe u v
variable {A : Type u} {X : Type v}
variable [Ring A] [AddCommGroup X] [Module A X]
namespace PretorsionImageClosed
theorem _root_.solution
    (I : Ideal (Module.End A X)) [I.IsTwoSided]
    (K : Submodule A X)
    (hK : ∀ f : Module.End A X, Submodule.map f K ≤ K)
    (hI : IsNilpotent I)
    (hinf : K ⊓ idealKernel I = ⊥) :
    K = ⊥ := by
  have hpowers :
      ∀ n : ℕ, K ⊓ idealKernel (I ^ n) = ⊥ := by
    intro n
    induction n with
    | zero =>
        rw [Submodule.pow_zero, Ideal.one_eq_top, idealKernel_top,
          inf_bot_eq]
    | succ n hn =>
        apply le_bot_iff.mp
        intro x hx
        have hxK : x ∈ K := hx.1
        have hxkerI : x ∈ idealKernel I := by
          rw [idealKernel, Submodule.mem_iInf]
          rintro ⟨q, hq⟩
          rw [LinearMap.mem_ker]
          have hqxK : q x ∈ K := by
            exact hK q ⟨x, hxK, rfl⟩
          have hqxker : q x ∈ idealKernel (I ^ n) := by
            rw [idealKernel, Submodule.mem_iInf]
            rintro ⟨p, hp⟩
            rw [LinearMap.mem_ker]
            have hpq : p * q ∈ I ^ (n + 1) := by
              rw [Submodule.pow_succ]
              exact Ideal.mul_mem_mul hp hq
            have hzero :=
              idealKernel_le_ker (p * q) hpq hx.2
            rw [LinearMap.mem_ker, Module.End.mul_eq_comp,
              LinearMap.comp_apply] at hzero
            exact hzero
          have hzero : q x = 0 := by
            have hmem : q x ∈
                K ⊓ idealKernel (I ^ n) :=
              ⟨hqxK, hqxker⟩
            rw [hn] at hmem
            exact hmem
          exact hzero
        have hxbot : x ∈ (⊥ : Submodule A X) := by
          rw [← hinf]
          exact ⟨hxK, hxkerI⟩
        exact hxbot
  obtain ⟨n, hn⟩ := hI
  have hfinal := hpowers n
  have hnbot : I ^ n = ⊥ := by
    simpa only [Ideal.zero_eq_bot] using hn
  rw [hnbot, idealKernel_bot, inf_top_eq] at hfinal
  exact hfinal
end PretorsionImageClosed
