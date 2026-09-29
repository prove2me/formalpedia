-- Prove2me | solution 1 for Real.abs_one_sub_exp_inv_eq_exp_neg_mul_abs_one_sub_exp_and_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/725a1ad1-da31-5c31-94cf-27420f13edde

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Real_abs_one_sub_exp_inv_eq_exp_neg_mul_abs_one_sub_exp_and_contDiff

set_option autoImplicit false

theorem solution :
    (∀ X : ℝ, |1 - (Real.exp X)⁻¹| = Real.exp (-X) * |1 - Real.exp X|) ∧
    (∀ X : ℝ, |1 - (-Real.exp X)⁻¹| = 1 + Real.exp (-X)) ∧
    (∀ X : ℝ, 0 < 1 + Real.exp (-X)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun X : ℝ => 1 + Real.exp (-X)) := by
  refine ⟨fun X => ?_, fun X => ?_, fun X => by positivity, ?_⟩
  · rw [← Real.exp_neg]
    have h : (1 : ℝ) - Real.exp (-X) = Real.exp (-X) * (Real.exp X - 1) := by
      rw [mul_sub, mul_one, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [h, abs_mul, abs_of_pos (Real.exp_pos _), abs_sub_comm]
  · rw [inv_neg, sub_neg_eq_add, ← Real.exp_neg, abs_of_pos (by positivity)]
  · exact contDiff_const.add (Real.contDiff_exp.comp contDiff_neg)

end S_Real_abs_one_sub_exp_inv_eq_exp_neg_mul_abs_one_sub_exp_and_contDiff
end P2MW
export P2MW.S_Real_abs_one_sub_exp_inv_eq_exp_neg_mul_abs_one_sub_exp_and_contDiff (solution)
