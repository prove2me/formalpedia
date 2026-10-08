-- Prove2me | solution 1 for RhinViola.shiftedZetaTwoTail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T11:32:22.904959+00:00
-- url     : https://prove2.me/submissions/b7c95ad8-3458-4b7b-bdc8-7c352c65ff7b

import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

theorem solution (h : ℕ) :
    HasSum (fun k : ℕ => (1 : ℝ) / (((k + h + 1 : ℕ) : ℝ) ^ 2))
      (Real.pi ^ 2 / 6 -
        Finset.sum (Finset.range (h + 1)) (fun j : ℕ =>
          (1 : ℝ) / (((j : ℕ) : ℝ) ^ 2))) := by
  let f : ℕ → ℝ := fun n => (1 : ℝ) / ((n : ℝ) ^ 2)
  change HasSum (fun k : ℕ => f (k + (h + 1)))
    (Real.pi ^ 2 / 6 - Finset.sum (Finset.range (h + 1)) (fun j : ℕ => f j))
  rw [hasSum_nat_add_iff]
  simpa [f] using hasSum_zeta_two
