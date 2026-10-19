-- Prove2me | solution 1 for actuarial_c_variance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:05:36.649982+00:00
-- url     : https://prove2.me/submissions/7991da33-d77f-46bd-bc57-9ace711b7f7e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_second
import Definitions.Def_actuarial_c_variance

open ActuarialAssurances


theorem solution (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hm : total h p=1) : 0 ≤ variance h v b p := by
  unfold variance second epv
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = ∑ k ∈ Finset.range (h+1), p k * path h v b k := ⟨_, rfl⟩
  have hnn : 0 ≤ ∑ k ∈ Finset.range (h+1), p k * (path h v b k - μ)^2 :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hp k) (sq_nonneg _))
  have e : ∑ k ∈ Finset.range (h+1), p k * (path h v b k - μ)^2 =
      ∑ k ∈ Finset.range (h+1), p k * (path h v b k)^2 - 2 * μ * (∑ k ∈ Finset.range (h+1), p k * path h v b k)
        + μ^2 * (∑ k ∈ Finset.range (h+1), p k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  unfold total at hm
  rw [← hμ, hm] at e
  rw [← hμ]
  nlinarith

