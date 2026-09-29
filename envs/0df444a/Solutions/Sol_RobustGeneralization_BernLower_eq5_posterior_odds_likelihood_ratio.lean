-- Prove2me | solution 1 for RobustGeneralization.BernLower.eq5_posterior_odds_likelihood_ratio
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:51:29.393755+00:00
-- url     : https://prove2.me/submissions/be75e515-9c64-4057-a3e8-6b8b426760f5

import Mathlib
import Definitions.Def_RobustGeneralization_BernLower_Model

namespace RobustGeneralization.BernLower

theorem aux_eq5odds_bern1W_pos (θ : Bool) (τ : ℝ) (hτ : 0 < τ) (hτ' : τ < 1 / 2)
    (p : Bool × Bool) : 0 < bern1W θ τ p := by
  have ha : (0 : ℝ) < 1 / 2 + τ := by linarith
  have hb : (0 : ℝ) < 1 / 2 - τ := by linarith
  unfold bern1W
  split_ifs
  · exact mul_pos (by norm_num) ha
  · exact mul_pos (by norm_num) hb

end RobustGeneralization.BernLower

open RobustGeneralization.BernLower

theorem solution (n : ℕ) (τ : ℝ) (hτ : 0 < τ) (hτ' : τ < 1 / 2)
    (S : Fin n → Bool × Bool) :
    odds1 τ S = ∏ k, ((1 / 2 + τ) / (1 / 2 - τ)) ^ (lab (S k).2 * lab (S k).1) := by
  have ha : (0 : ℝ) < 1 / 2 + τ := by linarith
  have hb : (0 : ℝ) < 1 / 2 - τ := by linarith
  have hJ : ∀ θ, 0 < joint1 τ θ S := fun θ => by
    unfold joint1
    exact mul_pos (by norm_num)
      (Finset.prod_pos fun k _ => aux_eq5odds_bern1W_pos θ τ hτ hτ' (S k))
  have hD : (∑ θ : Bool, joint1 τ θ S) ≠ 0 := by
    rw [Fintype.sum_bool]
    exact ne_of_gt (add_pos (hJ true) (hJ false))
  unfold odds1 post1
  rw [div_div_div_cancel_right₀ hD]
  unfold joint1
  rw [mul_div_mul_left _ _ (by norm_num : (1 / 2 : ℝ) ≠ 0), ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro k _
  obtain ⟨x, y⟩ := S k
  cases x <;> cases y <;>
    simp [bern1W, lab, Real.rpow_neg_one, mul_div_mul_left _ _ (by norm_num : (2⁻¹ : ℝ) ≠ 0)]
