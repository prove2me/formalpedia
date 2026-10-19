-- Prove2me | solution 1 for actuarial_c_endowment_variance_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:01:18.747853+00:00
-- url     : https://prove2.me/submissions/e9566817-4c8b-4b72-bd96-0e4c06fbedc5

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_purePath
import Definitions.Def_actuarial_c_endowPath
import Definitions.Def_actuarial_c_endow
import Definitions.Def_actuarial_c_endowSecond
import Definitions.Def_actuarial_c_endowVariance

open ActuarialAssurances


theorem solution (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hm : total h p = 1) : 0 ≤ endowVariance h n v b p := by
  unfold endowVariance endowSecond endow
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = ∑ k ∈ Finset.range (h+1), p k * endowPath h n v b k := ⟨_, rfl⟩
  have hnn : 0 ≤ ∑ k ∈ Finset.range (h+1), p k * (endowPath h n v b k - μ)^2 :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hp k) (sq_nonneg _))
  have e : ∑ k ∈ Finset.range (h+1), p k * (endowPath h n v b k - μ)^2 =
      ∑ k ∈ Finset.range (h+1), p k * (endowPath h n v b k)^2 - 2 * μ * (∑ k ∈ Finset.range (h+1), p k * endowPath h n v b k)
        + μ^2 * (∑ k ∈ Finset.range (h+1), p k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  unfold total at hm
  rw [← hμ, hm] at e
  rw [← hμ]
  nlinarith

