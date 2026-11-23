-- Prove2me | solution 1 for PNormReg.run_work_le
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:57:21.172367+00:00
-- url     : https://prove2.me/submissions/e7baff5e-95eb-44c1-8d62-cf48e8d208cc

import Mathlib
import Definitions.Def_PNormReg_Machine

open PNormReg

namespace PNormRegRunWorkLeAux

lemma run_succ (P : Program) (s : State) (ω : ℕ → Bool) (t : ℕ) :
    run P s ω (t + 1) = run P (step P ω s) ω t := by
  simp only [run, Function.iterate_succ_apply]

lemma step_work_le (P : Program) (s : State) (ω : ℕ → Bool) :
    (step P ω s).work ≤ s.work + 1 := by
  by_cases h : s.halted = true
  · simp [step, h]
  · rw [step, if_neg h]
    split <;> simp

end PNormRegRunWorkLeAux

open PNormRegRunWorkLeAux

theorem solution (P : Program) (s : State) (ω : ℕ → Bool) (t : ℕ) :
    (run P s ω t).work ≤ s.work + t := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    rw [PNormRegRunWorkLeAux.run_succ]
    calc
      (run P (step P ω s) ω t).work ≤ (step P ω s).work + t := ih (step P ω s)
      _ ≤ (s.work + 1) + t := Nat.add_le_add_right (step_work_le P s ω) t
      _ = s.work + (t + 1) := by omega