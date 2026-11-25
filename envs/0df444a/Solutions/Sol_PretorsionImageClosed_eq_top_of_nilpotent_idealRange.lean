-- Prove2me | solution 1 for PretorsionImageClosed.eq_top_of_nilpotent_idealRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:38:09.56626+00:00
-- url     : https://prove2.me/submissions/d6694293-9eae-4c0b-ade5-c622a715e512

module
public import Mathlib.RingTheory.Artinian.Ring
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Theorems.Thm_PretorsionImageClosed_mem_endNonunitsIdeal_iff
public import Theorems.Thm_PretorsionImageClosed_idealRange_bot
public import Theorems.Thm_PretorsionImageClosed_idealRange_top
public import Theorems.Thm_PretorsionImageClosed_map_idealRange_le
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
    (T : Submodule A X)
    (hT : ∀ f : Module.End A X, Submodule.map f T ≤ T)
    (hI : IsNilpotent I)
    (hsup : T ⊔ idealRange I = ⊤) :
    T = ⊤ := by
  have hpowers :
      ∀ n : ℕ, T ⊔ idealRange (I ^ n) = ⊤ := by
    intro n
    induction n with
    | zero =>
        rw [Submodule.pow_zero, Ideal.one_eq_top, idealRange_top,
          sup_top_eq]
    | succ n hn =>
        apply top_unique
        rw [← hn]
        apply sup_le
        · exact le_sup_left
        apply iSup_le
        rintro ⟨f, hf⟩
        rw [← Submodule.map_top, ← hsup, Submodule.map_sup]
        apply sup_le_sup
        · exact hT f
        · rw [Submodule.pow_succ]
          exact map_idealRange_le f hf
  obtain ⟨n, hn⟩ := hI
  have hfinal := hpowers n
  have hnbot : I ^ n = ⊥ := by
    simpa only [Ideal.zero_eq_bot] using hn
  rw [hnbot, idealRange_bot, sup_bot_eq] at hfinal
  exact hfinal
end PretorsionImageClosed
