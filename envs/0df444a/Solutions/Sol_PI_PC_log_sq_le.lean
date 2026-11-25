-- Prove2me | solution 1 for PI.PC.log_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:04:07.288791+00:00
-- url     : https://prove2.me/submissions/21408310-5077-4a28-bde9-96b246b07c94

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_ChebyshevPrimeBoundsLogFact
import Theorems.Thm_PI_PC_log_131072_eq_seventeen_mul_log_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PC
open Real MeasureTheory Set
namespace PI.PC
theorem _root_.solution {x : ℝ} (hx : 131072 ≤ x) : log x ^ 2 ≤ 0.00106 * x := by
  have hq : 1 ≤ x / 131072 := by rw [le_div_iff₀ (by norm_num)]; linarith
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (x / 131072) := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by
    rw [hsdef]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (x / 131072) := by
        first | exact Real.sqrt_le_sqrt hq | exact Real.sqrt_le_sqrt (by exact hq) | gcongr
  have hss : s ^ 2 = x / 131072 := by rw [hsdef]; exact Real.sq_sqrt (by linarith)
  have hxs : x = 131072 * s ^ 2 := by rw [hss]; ring
  have hlogs : log s ≤ s - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlogx : log x = log 131072 + 2 * log s := by
    rw [hxs, Real.log_mul (by norm_num) (pow_pos (by linarith) 2).ne', Real.log_pow]; norm_num
  have hl2 : log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hl2' : 0.6931471803 < log 2 := Real.log_two_gt_d9
  have hup : log x ≤ 17 * log 2 - 2 + 2 * s := by rw [hlogx, log_131072_eq_seventeen_mul_log_two]; linarith
  have hlow : 0 ≤ log x := Real.log_nonneg (by linarith)
  have hA0 : 0 ≤ 17 * log 2 - 2 := by linarith
  have h1 : 17 * log 2 - 2 + 2 * s ≤ (17 * log 2) * s := by
    nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hs1)]
  have h2 : 0 ≤ 17 * log 2 - 2 + 2 * s := by linarith
  have hsq2 : log 2 ^ 2 ≤ 0.6931471808 ^ 2 := pow_le_pow_left₀ (by linarith) hl2.le 2
  have h3 : (17 * log 2) ^ 2 ≤ 138.86 := by nlinarith [hsq2]
  calc log x ^ 2 ≤ (17 * log 2 - 2 + 2 * s) ^ 2 := pow_le_pow_left₀ hlow hup 2
    _ ≤ ((17 * log 2) * s) ^ 2 := pow_le_pow_left₀ h2 h1 2
    _ = (17 * log 2) ^ 2 * s ^ 2 := by ring
    _ ≤ 138.86 * s ^ 2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg s)
    _ ≤ 0.00106 * (131072 * s ^ 2) := by nlinarith [sq_nonneg s]
    _ = 0.00106 * x := by rw [← hxs]
end PI.PC
