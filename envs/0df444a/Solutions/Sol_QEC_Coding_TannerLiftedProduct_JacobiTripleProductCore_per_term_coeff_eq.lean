-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.per_term_coeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:55:38.394905+00:00
-- url     : https://prove2.me/submissions/594c98c9-f884-4d57-8ede-66598814ca18

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_pow_mul_Q__pow_eq_single_f8efc88f6b2b
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_exponent_identity
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore___expression_eq_single_mul_V_dfa183ee7d29
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_single_mul

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j d ℓ : ℕ) :
    (PowerSeries.coeff d)
      ((-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    ((-A_hahn j) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ).coeff
      ((d : ℤ) - ((j + 1 : ℤ)) ^ 2) := by
  set N_val := (-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ with hN_def
  rw [show (PowerSeries.coeff d)
      ((-1 : R) ^ ℓ * q ^ N_val * PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    (ι_hahn ((-1 : R) ^ ℓ * q ^ N_val * PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1)).coeff (d : ℤ)
    from (HahnSeries.ofPowerSeries_apply_coeff _ _).symm]
  rw [ι_expression_eq_single_mul_V j ℓ]
  have hN_eq : (↑N_val : ℤ) = (↑j + 1) ^ 2 + (-2 * ↑j * ↑ℓ + 2 * ↑(ℓ.choose 2)) := by
    rw [hN_def]
    push_cast
    have h := exponent_identity j ℓ
    rw [Int.natAbs_sq] at h
    rw [sq_abs]
    linarith
  rw [show HahnSeries.single (↑N_val : ℤ) ((-1 : LaurentPolynomial ℤ) ^ ℓ) =
    HahnSeries.single ((j + 1 : ℤ) ^ 2) (1 : LaurentPolynomial ℤ) *
    HahnSeries.single (-2 * ↑j * ↑ℓ + 2 * ↑(ℓ.choose 2) : ℤ) ((-1 : LaurentPolynomial ℤ) ^ ℓ) by
      rw [HahnSeries.single_mul_single, one_mul, hN_eq]]
  rw [mul_assoc, coeff_single_mul, neg_A_pow_mul_Q₀_pow_eq_single]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
