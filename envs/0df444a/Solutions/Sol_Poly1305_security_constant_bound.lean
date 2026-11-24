-- Prove2me | solution 1 for Poly1305.security_constant_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-24T08:05:01.864732+00:00
-- url     : https://prove2.me/submissions/d7081cc3-d654-42f7-a525-275e4acc1a9e

import Mathlib.Analysis.SpecialFunctions.Pow.Real

section
section
namespace Poly1305.DefsConst

theorem exp_le : Real.exp (5001 / 10000) ≤ 1.649 := by
  have h := Real.exp_bound (x := 5001 / 10000) (by rw [abs_of_pos (by norm_num)]; norm_num)
    (n := 8) (by norm_num)
  have h2 := (abs_le.mp h).2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 5001 / 10000)] at h2
  norm_num at h2
  linarith

theorem exponent_le (C : ℝ) (hC0 : 0 ≤ C) (hC : C ≤ 2 ^ 64) :
    Real.log (1 - C / 2 ^ 128) * (-(C + 1) / 2) ≤ 5001 / 10000 := by
  set x : ℝ := 1 - C / 2 ^ 128 with hxdef
  have hx0 : 0 < x := by
    rw [hxdef]
    have : C / 2 ^ 128 ≤ 2 ^ 64 / 2 ^ 128 := by gcongr
    have : (2 : ℝ) ^ 64 / 2 ^ 128 < 1 := by norm_num
    linarith
  have hlog : -Real.log x ≤ 1 / x - 1 := by
    have := Real.log_le_sub_one_of_pos (one_div_pos.mpr hx0)
    rw [one_div, Real.log_inv] at this; rwa [one_div]
  have hstep : (C + 1) * (1 / x - 1) ≤ 2 * (5001 / 10000) := by
    have e : 1 / x - 1 = (C / 2 ^ 128) / x := by
      field_simp
      rw [hxdef]; ring
    rw [e, ← mul_div_assoc, div_le_iff₀ hx0, hxdef]
    have hCC : C * C ≤ 2 ^ 64 * 2 ^ 64 := by nlinarith
    nlinarith
  have hC1 : 0 ≤ (C + 1) / 2 := by positivity
  calc Real.log x * (-(C + 1) / 2) = (C + 1) / 2 * (-Real.log x) := by ring
    _ ≤ (C + 1) / 2 * (1 / x - 1) := mul_le_mul_of_nonneg_left hlog hC1
    _ ≤ 5001 / 10000 := by nlinarith

end Poly1305.DefsConst

namespace Poly1305

theorem security_constant_bound_dev :
    (∀ C : ℕ, C ≤ 2 ^ 64 →
      (1 - (C : ℝ) / 2 ^ 128) ^ (-((C : ℝ) + 1) / 2) ≤ 1.649) ∧
    (1.649 : ℝ) * 8 < 14 := by
  refine ⟨fun C hC => ?_, by norm_num⟩
  have hCr : (C : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hC
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hx0 : (0 : ℝ) < 1 - (C : ℝ) / 2 ^ 128 := by
    have : (C : ℝ) / 2 ^ 128 ≤ 2 ^ 64 / 2 ^ 128 := by gcongr
    have : (2 : ℝ) ^ 64 / 2 ^ 128 < 1 := by norm_num
    linarith
  rw [Real.rpow_def_of_pos hx0]
  calc Real.exp (Real.log (1 - (C : ℝ) / 2 ^ 128) * (-((C : ℝ) + 1) / 2))
      ≤ Real.exp (5001 / 10000) := Real.exp_le_exp.mpr (DefsConst.exponent_le C hC0 hCr)
    _ ≤ 1.649 := DefsConst.exp_le

end Poly1305

end
end

section
open Poly1305

theorem solution :
    (∀ C : ℕ, C ≤ 2 ^ 64 →
      (1 - (C : ℝ) / 2 ^ 128) ^ (-((C : ℝ) + 1) / 2) ≤ 1.649) ∧
    (1.649 : ℝ) * 8 < 14 := by
  apply Poly1305.security_constant_bound_dev <;> assumption

end
