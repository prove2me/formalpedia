-- Prove2me | solution 1 for PNormReg.run_work_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:00:06.092485+00:00
-- url     : https://prove2.me/submissions/bcfbf4b6-c4c0-441b-aae8-7e5c2910ad02

import Mathlib
import Definitions.Def_PNormReg_Machine

open PNormReg

namespace PNormRegRunWorkEqAux

lemma run_succ (P : Program) (s : State) (ω : ℕ → Bool) (t : ℕ) :
    run P s ω (t + 1) = run P (step P ω s) ω t := by
  simp only [run, Function.iterate_succ_apply]

lemma run_of_halted {P : Program} {ω : ℕ → Bool} {s : State} (h : s.halted = true) :
    ∀ t, run P s ω t = s
  | 0 => rfl
  | t + 1 => by rw [run_succ, show step P ω s = s by simp [step, h]]; exact run_of_halted h t

lemma step_work_of_running {P : Program} {ω : ℕ → Bool} {s : State}
    (h : s.halted = false) : (step P ω s).work = s.work + 1 := by
  rw [step, if_neg (by simp [h])]
  split <;> rfl

end PNormRegRunWorkEqAux

open PNormRegRunWorkEqAux

theorem solution (P : Program) (s : State) (ω : ℕ → Bool) (t : ℕ)
    (h₀ : s.halted = false) (hₜ : (run P s ω t).halted = false) :
    (run P s ω t).work = s.work + t := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    rw [PNormRegRunWorkEqAux.run_succ] at hₜ ⊢
    have hs : (step P ω s).halted = false := by
      by_cases h : (step P ω s).halted = true
      · rw [PNormRegRunWorkEqAux.run_of_halted h t] at hₜ
        rw [h] at hₜ
        exact Bool.noConfusion hₜ
      · exact Bool.eq_false_of_not_eq_true h
    rw [ih (step P ω s) hs hₜ, step_work_of_running h₀]
    omega