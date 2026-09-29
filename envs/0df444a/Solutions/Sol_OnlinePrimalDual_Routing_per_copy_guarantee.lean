-- Prove2me | solution 1 for OnlinePrimalDual.Routing.per_copy_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:45:46.474712+00:00
-- url     : https://prove2.me/submissions/2907f8d3-bad2-4b93-b7b1-81556a64cf00

import Mathlib

namespace OnlinePrimalDual.Routing

theorem aux_pcg_log_bound (u : ℝ) (hu : 1 ≤ u) :
    Real.log 2 / u ≤ Real.log (1 + 1 / u) := by
  have hu0 : 0 < u := by linarith
  have h1 : (0:ℝ) ≤ 1 / u := by positivity
  have h2 : 1 / u ≤ 1 := by rw [div_le_one hu0]; exact hu
  have hb := rpow_one_add_le_one_add_mul_self (s := (1:ℝ)) (by norm_num) h1 h2
  have h3 : ((1:ℝ) + 1) ^ (1 / u) = (2:ℝ) ^ (1 / u) := by norm_num
  rw [h3, mul_one] at hb
  have hpos : (0:ℝ) < (2:ℝ) ^ (1 / u) := by positivity
  have := Real.log_le_log hpos hb
  rw [Real.log_rpow (by norm_num : (0:ℝ) < 2)] at this
  calc Real.log 2 / u = 1 / u * Real.log 2 := by ring
    _ ≤ _ := this

end OnlinePrimalDual.Routing

open OnlinePrimalDual.Routing

theorem solution
    (M uMin stepB stepC : ℝ)
    (huMin_pos : 0 < uMin) (hstepB_nonneg : 0 ≤ stepB) (hstepC_nonneg : 0 ≤ stepC)
    (hstepC_le_uMin : stepC ≤ uMin)
    (hweak_duality : M - uMin ≤ stepB)
    (hstepC_fills : min uMin (M - stepB) ≤ stepC)
    (uCap m n R : ℝ)
    (hm_pos : 0 < m) (hn_pos : 0 < n) (huCap_pos : 0 < uCap) (huCap_ge_one : 1 ≤ uCap)
    (hmn : m ≤ n ^ 2) (huCap_le : uCap ≤ m ^ 2 * uMin)
    (hR_nonneg : 0 ≤ R) (hx_bound : uMin / (m * uCap) * (1 + 1 / uCap) ^ R ≤ 2) :
    M ≤ stepB + stepC ∧ R ≤ uCap * (2 + 6 * Real.logb 2 n) := by
  constructor
  · rcases min_choice uMin (M - stepB) with h | h
    · rw [h] at hstepC_fills; linarith
    · rw [h] at hstepC_fills; linarith
  · have hA : 0 < uMin / (m * uCap) := by positivity
    have hP : 0 < (1 + 1 / uCap) ^ R := by positivity
    have hlog := Real.log_le_log (mul_pos hA hP) hx_bound
    rw [Real.log_mul hA.ne' hP.ne', Real.log_rpow (by positivity),
      Real.log_div huMin_pos.ne' (mul_pos hm_pos huCap_pos).ne',
      Real.log_mul hm_pos.ne' huCap_pos.ne'] at hlog
    have hlu : Real.log uCap ≤ 2 * Real.log m + Real.log uMin := by
      have := Real.log_le_log huCap_pos huCap_le
      rwa [Real.log_mul (by positivity) huMin_pos.ne', Real.log_pow] at this
    have hlm : Real.log m ≤ 2 * Real.log n := by
      have := Real.log_le_log hm_pos hmn
      rwa [Real.log_pow] at this
    have hkey := aux_pcg_log_bound uCap huCap_ge_one
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hRb : R * (Real.log 2 / uCap) ≤ Real.log 2 + 6 * Real.log n := by
      have := mul_le_mul_of_nonneg_left hkey hR_nonneg
      nlinarith
    have hRb2 : R * Real.log 2 ≤ uCap * (Real.log 2 + 6 * Real.log n) := by
      have e : R * (Real.log 2 / uCap) = R * Real.log 2 / uCap := by ring
      rw [e, div_le_iff₀ huCap_pos] at hRb
      linarith
    rw [Real.logb]
    rw [show uCap * (2 + 6 * (Real.log n / Real.log 2))
        = (uCap * (Real.log 2 + 6 * Real.log n) + uCap * Real.log 2) / Real.log 2 by
          field_simp; ring]
    rw [le_div_iff₀ hl2]
    nlinarith
