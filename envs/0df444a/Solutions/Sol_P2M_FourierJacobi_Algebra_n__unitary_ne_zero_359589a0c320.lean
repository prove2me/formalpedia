-- Prove2me | solution 1 for P2M_FourierJacobi_Algebra_n__unitary_ne_zero_359589a0c320
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:59:20.64605+00:00
-- url     : https://prove2.me/submissions/d4e2e7eb-7834-4b51-9b17-a59952fb1b06

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Theorems.Thm_FourierJacobi_Algebra_coe_pow_norm_lt_one
import Theorems.Thm_FourierJacobi_Algebra_one_sub_mul_ne_zero_of_norm_lt_one


set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution {t : ℝ} {a b : ℂ}
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    n₂ (t : ℂ) a b ≠ 0 := by
  have hx := coe_pow_norm_lt_one ht₀ ht₁ (by decide : (2 : ℕ) ≠ 0)
  have hab : ‖a * b‖ = 1 := by simp [ha, hb]
  have hab' : ‖a / b‖ = 1 := by simp [ha, hb]
  have hba : ‖b / a‖ = 1 := by simp [ha, hb]
  have hi : ‖(a * b)⁻¹‖ = 1 := by simp [ha, hb]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (by simpa [mul_assoc] using one_sub_mul_ne_zero_of_norm_lt_one hab hx)
    (one_sub_mul_ne_zero_of_norm_lt_one hab' hx))
    (one_sub_mul_ne_zero_of_norm_lt_one hba hx))
    (one_sub_mul_ne_zero_of_norm_lt_one hi hx)
end FourierJacobi.Algebra
