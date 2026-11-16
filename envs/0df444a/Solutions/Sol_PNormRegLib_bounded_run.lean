-- Prove2me | solution 1 for PNormRegLib.bounded_run
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-15T08:14:26.395927+00:00
-- url     : https://prove2.me/submissions/1c04d78d-a49d-46e9-b14a-c611fb40bb6a

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_PNormRegLib_AddressBound
import Theorems.Thm_PNormRegLib_step_eq_exec

open PNormReg PNormRegLib

namespace PNormRegLibBoundAux

lemma two_mul_abs {a X : ℤ} (h : |a| ≤ X) (hX : 0 ≤ X) : |a| ≤ 2 * X := by linarith

lemma bounded_exec {ω : ℕ → Bool} {ins : Instr} {X : ℤ} {s : State} (hs : PBounded X s)
    (hlit : ∀ q c, ins = .core (.pset q c) → |c| ≤ X) (hX : 1 ≤ X) :
    PBounded (2 * X) (exec ω ins s) := by
  obtain ⟨hp, hi⟩ := hs
  have hX0 : (0 : ℤ) ≤ X := by linarith
  have hp2 : ∀ q, |s.core.ptrs q| ≤ 2 * X := fun q => two_mul_abs (hp q) hX0
  have hi2 : ∀ z, |s.integerMemory z| ≤ 2 * X := fun z => two_mul_abs (hi z) hX0
  have upd : ∀ (f : ℤ → ℤ) (q : ℤ) (x : ℤ), (∀ z, |f z| ≤ 2 * X) → |x| ≤ 2 * X →
      ∀ z, |Function.update f q x z| ≤ 2 * X := by
    intro f q x hf hx z
    rw [Function.update_apply]; split_ifs
    · exact hx
    · exact hf z
  have updn : ∀ (f : ℕ → ℤ) (q : ℕ) (x : ℤ), (∀ z, |f z| ≤ 2 * X) → |x| ≤ 2 * X →
      ∀ z, |Function.update f q x z| ≤ 2 * X := by
    intro f q x hf hx z
    rw [Function.update_apply]; split_ifs
    · exact hx
    · exact hf z
  cases ins with
  | core i =>
    cases i with
    | pset q c => exact ⟨updn _ _ _ hp2 (two_mul_abs (hlit q c rfl) hX0), hi2⟩
    | pcopy q q' => exact ⟨updn _ _ _ hp2 (hp2 q'), hi2⟩
    | pinc q =>
      refine ⟨updn _ _ _ hp2 ?_, hi2⟩
      have := abs_le.mp (hp q); rw [abs_le]; constructor <;> linarith
    | pdec q =>
      refine ⟨updn _ _ _ hp2 ?_, hi2⟩
      have := abs_le.mp (hp q); rw [abs_le]; constructor <;> linarith
    | jle i t =>
      simp only [exec, coreExec]; split_ifs <;> exact ⟨hp2, hi2⟩
    | pjle q q' t =>
      simp only [exec, coreExec]; split_ifs <;> exact ⟨hp2, hi2⟩
    | _ => exact ⟨hp2, hi2⟩
  | pointerAdd d a b =>
    refine ⟨updn _ _ _ hp2 ?_, hi2⟩
    have := abs_le.mp (hp a); have := abs_le.mp (hp b); rw [abs_le]; constructor <;> linarith
  | pointerSub d a b =>
    refine ⟨updn _ _ _ hp2 ?_, hi2⟩
    have := abs_le.mp (hp a); have := abs_le.mp (hp b); rw [abs_le]; constructor <;> linarith
  | integerLoad d a => exact ⟨updn _ _ _ hp2 (hi2 _), hi2⟩
  | integerStore a b => exact ⟨hp2, upd _ _ _ hi2 (hp2 b)⟩
  | _ => exact ⟨hp2, hi2⟩

lemma bounded_step {P : Program} {ω : ℕ → Bool} {X : ℤ} {s : State} (hs : PBounded X s)
    (hlit : LitBound P X) (hX : 1 ≤ X) : PBounded (2 * X) (step P ω s) := by
  have hX0 : (0 : ℤ) ≤ X := by linarith
  by_cases hh : s.halted = true
  · rw [show step P ω s = s by simp [step, hh]]
    exact ⟨fun q => two_mul_abs (hs.1 q) hX0, fun z => two_mul_abs (hs.2 z) hX0⟩
  · simp only [Bool.not_eq_true] at hh
    cases h : P[s.core.pc]? with
    | none =>
      rw [show step P ω s = { s with work := s.work + 1 } by simp [step, hh, h]]
      exact ⟨fun q => two_mul_abs (hs.1 q) hX0, fun z => two_mul_abs (hs.2 z) hX0⟩
    | some ins =>
      rw [step_eq_exec P ω s ins hh h]
      refine bounded_exec hs (fun q c hc => hlit q c ?_) hX
      subst hc; exact List.mem_of_getElem? h

end PNormRegLibBoundAux

open PNormRegLibBoundAux in
theorem solution (P : Program) (ω : ℕ → Bool) (X : ℤ) (s : State) (hs : PBounded X s)
    (hlit : LitBound P X) (hX : 1 ≤ X) (t : ℕ) : PBounded (X * 2 ^ t) (run P s ω t) := by
  induction t with
  | zero => simpa [run] using hs
  | succ t ih =>
    have hpow : (1 : ℤ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
    have h1 : (1 : ℤ) ≤ X * 2 ^ t := by nlinarith
    have hstep := bounded_step (ω := ω) ih
      (fun q c hc => (hlit q c hc).trans (by nlinarith)) h1
    have e : run P s ω (t + 1) = step P ω (run P s ω t) := by
      simp only [run, Function.iterate_succ_apply']
    rw [e, pow_succ, show X * (2 ^ t * 2) = 2 * (X * 2 ^ t) by ring]
    exact hstep
