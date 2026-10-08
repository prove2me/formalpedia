-- Prove2me | solution 1 for SuttonBartoRL.FiniteMDP.return_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T12:38:16.368059+00:00
-- url     : https://prove2.me/submissions/8e1bec62-7f5c-4c43-9e07-cf5d65dac57f

import Mathlib
import Definitions.Def_SuttonBartoRL_FiniteMDP_MDP

lemma rr3d0414a8_summable (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (R : ℕ → ℝ)
    (hR : ∃ C : ℝ, ∀ k, |R k| ≤ C) (t : ℕ) :
    Summable (fun k : ℕ => γ ^ k * R (t + k + 1)) := by
  obtain ⟨C, hC⟩ := hR
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hγ0 hγ1).mul_left C) ?_
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 k), mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC _) (pow_nonneg hγ0 k)

open SuttonBartoRL.FiniteMDP in
theorem solution (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (R : ℕ → ℝ)
    (hR : ∃ C : ℝ, ∀ k, |R k| ≤ C) (t : ℕ) :
    Summable (fun k : ℕ => γ ^ k * R (t + k + 1)) ∧
      discountedReturn γ R t = R (t + 1) + γ * discountedReturn γ R (t + 1) := by
  refine ⟨rr3d0414a8_summable γ hγ0 hγ1 R hR t, ?_⟩
  unfold discountedReturn
  rw [(rr3d0414a8_summable γ hγ0 hγ1 R hR t).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero, pow_succ]
  congr 1
  refine tsum_congr fun k => ?_
  rw [show t + (k + 1) + 1 = t + 1 + k + 1 by omega]
  ring
