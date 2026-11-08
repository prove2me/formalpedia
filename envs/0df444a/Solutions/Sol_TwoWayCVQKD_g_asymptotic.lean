-- Prove2me | solution 1 for TwoWayCVQKD.g_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:31:21.953535+00:00
-- url     : https://prove2.me/submissions/014103a4-4378-4a9f-87c4-c1f22ad7866c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P49
open QAlgorithms.Papers.Independent.Information100.P49 (symplecticEntropy)
open Asymptotics Filter

namespace Aux_TwoWayCVQKD_g

lemma log_sub_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : Real.log y - Real.log x ≤ (y - x) / x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  have : y / x - 1 = (y - x) / x := by field_simp
  linarith

lemma log_sub_ge {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : (y - x) / y ≤ Real.log y - Real.log x := by
  have h := log_sub_le hy hx
  have : (x - y) / y = -((y - x) / y) := by ring
  linarith

end Aux_TwoWayCVQKD_g

open Aux_TwoWayCVQKD_g in
theorem solution :
    (fun ν : ℝ => symplecticEntropy ν - Real.log (Real.exp 1 * ν / 2)) =O[atTop]
      (fun ν : ℝ => ν⁻¹) := by
  refine IsBigO.of_bound 1 ((eventually_ge_atTop (2 : ℝ)).mono fun ν hν => ?_)
  have hν0 : 0 < ν := by linarith
  have hν1 : 0 < ν - 1 := by linarith
  have hν2 : 0 < ν + 1 := by linarith
  have hS : symplecticEntropy ν = ((ν + 1) / 2) * (Real.log (ν + 1) - Real.log 2)
      - ((ν - 1) / 2) * (Real.log (ν - 1) - Real.log 2) := by
    simp only [QAlgorithms.Papers.Independent.Information100.P49.symplecticEntropy,
      QAlgorithms.Papers.Independent.Information100.P49.thermalEntropy]
    rw [show (ν - 1) / 2 + 1 = (ν + 1) / 2 by ring, Real.log_div hν2.ne' two_ne_zero,
      Real.log_div hν1.ne' two_ne_zero]
  have hL : Real.log (Real.exp 1 * ν / 2) = 1 + Real.log ν - Real.log 2 := by
    rw [Real.log_div (by positivity) two_ne_zero, Real.log_mul (by positivity) hν0.ne',
      Real.log_exp]
  have a1 := log_sub_le hν0 hν2
  have a2 := log_sub_ge hν0 hν2
  have b1 := log_sub_le hν1 hν0
  have b2 := log_sub_ge hν1 hν0
  set d1 := Real.log (ν + 1) - Real.log ν with hd1
  set d2 := Real.log ν - Real.log (ν - 1) with hd2
  have e1 : (ν + 1 - ν) / ν = 1 / ν := by ring
  have e2 : (ν + 1 - ν) / (ν + 1) = 1 / (ν + 1) := by ring
  have e3 : (ν - (ν - 1)) / (ν - 1) = 1 / (ν - 1) := by ring
  have e4 : (ν - (ν - 1)) / ν = 1 / ν := by ring
  rw [e1] at a1; rw [e2] at a2; rw [e3] at b1; rw [e4] at b2
  have hE : symplecticEntropy ν - Real.log (Real.exp 1 * ν / 2)
      = ((ν + 1) * d1 + (ν - 1) * d2) / 2 - 1 := by
    rw [hS, hL, hd1, hd2]; ring
  rw [hE, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hν0, one_mul]
  have u1 : (ν + 1) * d1 ≤ 1 + 1 / ν := by
    have := mul_le_mul_of_nonneg_left a1 hν2.le
    have h' : (ν + 1) * (1 / ν) = 1 + 1 / ν := by field_simp
    linarith
  have u2 : (ν - 1) * d2 ≤ 1 := by
    have := mul_le_mul_of_nonneg_left b1 hν1.le
    have h' : (ν - 1) * (1 / (ν - 1)) = 1 := by field_simp
    linarith
  have l1 : 1 ≤ (ν + 1) * d1 := by
    have := mul_le_mul_of_nonneg_left a2 hν2.le
    have h' : (ν + 1) * (1 / (ν + 1)) = 1 := by field_simp
    linarith
  have l2 : 1 - 1 / ν ≤ (ν - 1) * d2 := by
    have := mul_le_mul_of_nonneg_left b2 hν1.le
    have h' : (ν - 1) * (1 / ν) = 1 - 1 / ν := by field_simp
    linarith
  have hinv : ν⁻¹ = 1 / ν := by ring
  have hpos : 0 < 1 / ν := by positivity
  rw [abs_le, hinv]
  constructor <;> linarith
