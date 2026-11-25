-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.cab_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:23:16.693983+00:00
-- url     : https://prove2.me/submissions/cfe6be3d-a022-4d13-b48a-d7c49ea3198b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_exp_quarter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (c gA : ℕ) (q t0 : ℝ) (hq : 2 ≤ q) (dst : ℝ) (hd : 0 ≤ dst)
    (hC5 : 4 * c * (7 + Real.log (q * c)) + dst + 1 ≤ t0) (hC6 : gA * Real.log 2 ≤ t0) :
    (5.12 : ℝ) ^ gA * (2 * (c + 1) / Real.pi) ^ c * Real.exp (5 * Real.pi * c) *
      Real.exp (-((Real.pi - 2) * t0)) ≤ 4 ^ gA := by
  have hpi := Real.pi_gt_d2
  have hpi4 := Real.pi_lt_d2
  have hl2 := Real.log_two_gt_d9

  have hc : (2 * (c + 1) / Real.pi) ^ c ≤ Real.exp (c * Real.log (q * c)) := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp
    · have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast h0
      have hqc : 0 < q * c := by positivity
      rw [Real.exp_nat_mul, Real.exp_log hqc]
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_iff₀ Real.pi_pos]; nlinarith
  have hlog : 0 ≤ c * Real.log (q * c) := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp
    · have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast h0
      exact mul_nonneg (by positivity) (Real.log_nonneg (by nlinarith))
  have hg : (5.12 : ℝ) ^ gA ≤ 4 ^ gA * Real.exp (gA / 4) := by
    have : (5.12 : ℝ) ^ gA = 4 ^ gA * 1.28 ^ gA := by rw [← mul_pow]; norm_num
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc (1.28 : ℝ) ^ gA ≤ Real.exp (1 / 4) ^ gA := pow_le_pow_left₀ (by norm_num) cab_exp_quarter gA
      _ = Real.exp (gA / 4) := by rw [← Real.exp_nat_mul]; ring_nf
  have hexp : Real.exp (gA / 4) * Real.exp (c * Real.log (q * c)) * Real.exp (5 * Real.pi * c) *
      Real.exp (-((Real.pi - 2) * t0)) ≤ 1 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_one_iff]
    have hcl : (c : ℝ) * Real.log (q * c) = c * Real.log (q * c) := rfl
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    have hg0 : (0 : ℝ) ≤ gA := Nat.cast_nonneg gA
    nlinarith [mul_le_mul_of_nonneg_left hC5 (by linarith : (0 : ℝ) ≤ (Real.pi - 2) / 2),
      mul_le_mul_of_nonneg_left hC6 (by linarith : (0 : ℝ) ≤ (Real.pi - 2) / 2)]
  calc (5.12 : ℝ) ^ gA * (2 * (c + 1) / Real.pi) ^ c * Real.exp (5 * Real.pi * c) *
        Real.exp (-((Real.pi - 2) * t0))
      ≤ (4 ^ gA * Real.exp (gA / 4)) * Real.exp (c * Real.log (q * c)) * Real.exp (5 * Real.pi * c) *
        Real.exp (-((Real.pi - 2) * t0)) := by gcongr
    _ = 4 ^ gA * (Real.exp (gA / 4) * Real.exp (c * Real.log (q * c)) * Real.exp (5 * Real.pi * c) *
        Real.exp (-((Real.pi - 2) * t0))) := by ring
    _ ≤ 4 ^ gA * 1 := by gcongr
    _ = 4 ^ gA := mul_one _
end ReciprocityTheory.ChartRestriction.G.I2
