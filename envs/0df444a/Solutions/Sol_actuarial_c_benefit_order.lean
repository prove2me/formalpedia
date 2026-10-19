-- Prove2me | solution 1 for actuarial_c_benefit_order
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:53:24.70603+00:00
-- url     : https://prove2.me/submissions/ec34948d-5580-40b9-b468-6f86a9294e8d

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv

open ActuarialAssurances


theorem solution (h : ℕ) (v : ℝ) (b c p : ℕ → ℝ) (hv : 0 ≤ v) (hp : ∀ j, 0 ≤ p j) (hbc : ∀ j, b j ≤ c j) : epv h v b p ≤ epv h v c p := by
  unfold epv path death
  apply Finset.sum_le_sum; intro k _
  apply mul_le_mul_of_nonneg_left _ (hp k)
  apply Finset.sum_le_sum; intro j _
  split_ifs
  · nlinarith [pow_nonneg hv (j+1), hbc j]
  · simp

