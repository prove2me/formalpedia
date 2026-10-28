-- Prove2me | solution 1 for actuarial_f_expect_scale
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:32:02.698735+00:00
-- url     : https://prove2.me/submissions/c592eb5f-e8cb-4af8-957c-daaef798070f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect

open ActuarialUnderpinsF

theorem solution (n h : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (f : ℕ → ℕ → ℕ → ℝ) (c : ℝ) :
    expect n h p (fun z i j => c * f z i j) = c * expect n h p f := by
  have msum : ∀ (s : Finset ℕ) (f : ℕ → ℝ) (c : ℝ), c * s.sum f = s.sum (fun x => c * f x) := by
    intro s f c
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, mul_add, ih]
  unfold expect ActuarialJointD.expect
  simp only [msum]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  grind
