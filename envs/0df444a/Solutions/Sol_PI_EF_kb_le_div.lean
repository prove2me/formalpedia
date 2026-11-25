-- Prove2me | solution 1 for PI.EF.kb_le_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:17.269331+00:00
-- url     : https://prove2.me/submissions/32939587-bc2e-4938-b149-b78e47cc8aa5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSumBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Finset
namespace PI.EF
theorem _root_.solution {u T x g : ℝ} (hu : 0 < u) (hT : 0 < T) (hx : 0 < x) (hx2 : x < 2 * u)
    (hg : 0 < g) (h : g ≤ |u - x|) : kb T (u / x) ≤ (4 * u / T) / g := by
  have hlog : g / (2 * u) ≤ |Real.log (u / x)| := by
    rcases le_or_gt x u with hxu | hxu
    · have h1 : 1 - x / u ≤ Real.log (u / x) := by
        have h0 := Real.one_sub_inv_le_log_of_pos (div_pos hu hx)
        rwa [inv_div] at h0
      have h2 : |u - x| = u - x := abs_of_nonneg (by linarith)
      rw [h2] at h
      have h3 : g / (2 * u) ≤ 1 - x / u := by
        rw [div_le_iff₀ (by positivity), sub_mul, div_mul_eq_mul_div, mul_div_assoc]
        have h4 : x * (2 * u) / u = 2 * x := by field_simp
        rw [mul_div_assoc] at h4
        nlinarith
      exact h3.trans (h1.trans (le_abs_self _))
    · have h1 : 1 - u / x ≤ Real.log (x / u) := by
        have h0 := Real.one_sub_inv_le_log_of_pos (div_pos hx hu)
        rwa [inv_div] at h0
      have e : |Real.log (u / x)| = Real.log (x / u) := by
        rw [Real.log_div hu.ne' hx.ne', Real.log_div hx.ne' hu.ne', abs_sub_comm,
          abs_of_nonneg (by linarith [Real.log_le_log hu hxu.le])]
      rw [e]
      have h2 : |u - x| = x - u := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      rw [h2] at h
      have h3 : g / (2 * u) ≤ 1 - u / x := by
        rw [div_le_iff₀ (by positivity)]
        have h4 : (1 - u / x) * (2 * u) = 2 * u - 2 * u * u / x := by ring
        rw [h4]
        have h5 : u * u / x ≤ u * u / u := div_le_div_of_nonneg_left (by positivity) hu hxu.le
        have h6 : u * u / u = u := by field_simp
        have h7 : 2 * u * u / x = 2 * (u * u / x) := by ring
        rw [h7]
        have h8 : (x - u) ≤ 2 * u - 2 * (u * u / x) := by
          have h9 : u * u / x ≤ u - (x - u) / 2 := by
            rw [div_le_iff₀ hx]
            nlinarith
          linarith
        linarith
      exact h3.trans h1
  unfold kb
  split_ifs with hk
  · rw [div_div, le_div_iff₀ (by positivity)]
    have hTg : T * (g / (2 * u)) ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hlog hT.le) hk
    rw [mul_div_assoc'] at hTg
    rw [div_le_one (by positivity)] at hTg
    nlinarith
  · push_neg at hk
    rw [div_div, one_div_le (by positivity) (by positivity), one_div_div]
    have hTg : T * (g / (2 * u)) ≤ T * |Real.log (u / x)| := mul_le_mul_of_nonneg_left hlog hT.le
    have e : T * g / (4 * u) ≤ T * (g / (2 * u)) := by
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ hT.le
      exact div_le_div_of_nonneg_left hg.le (by positivity) (by linarith)
    linarith
end PI.EF
