-- Prove2me | solution 1 for RhinViola.integerLinearFormHasSumFinset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T11:22:57.891925+00:00
-- url     : https://prove2.me/submissions/95ef750d-152f-459d-bcbe-a3f45311d926

import Theorems.Thm_RhinViola_integerLinearFormHasSumAdd
import Mathlib.Tactic

open scoped BigOperators

theorem solution
    {ι : Type*} [DecidableEq ι]
    (α : ℝ) (s : Finset ι) (f : ι → ℕ → ℝ) (z c : ι → ℤ)
    (h : ∀ i ∈ s, HasSum (f i) ((z i : ℝ) + (c i : ℝ) * α)) :
    HasSum (fun k : ℕ => Finset.sum s (fun i => f i k))
      (((Finset.sum s (fun i => z i) : ℤ) : ℝ) +
        ((Finset.sum s (fun i => c i) : ℤ) : ℝ) * α) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  | @insert a s ha ih =>
      have ha_sum : HasSum (f a) ((z a : ℝ) + (c a : ℝ) * α) := by
        exact h a (by simp)
      have hs :
          ∀ i ∈ s, HasSum (f i) ((z i : ℝ) + (c i : ℝ) * α) := by
        intro i hi
        exact h i (by simp [hi])
      have hs_sum := ih hs
      have hadd :=
        RhinViola.integerLinearFormHasSumAdd
          α (f a) (fun k : ℕ => Finset.sum s (fun i => f i k))
          (z a) (Finset.sum s (fun i => z i)) (c a) (Finset.sum s (fun i => c i))
          ha_sum hs_sum
      simpa [Finset.sum_insert, ha] using hadd
