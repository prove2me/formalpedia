-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.W_term_coeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:40:07.629197+00:00
-- url     : https://prove2.me/submissions/b0037383-825a-4aca-9f3d-55e856d1c7fb

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_Q__pow_fc719b7707f4
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_pow_mul_Q__pow_eq_single_general_095ffdd37216
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_single_mul_general

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j ℓ : ℕ) (b : ℤ) :
    ((-(A_hahn j * Q₀)) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ).coeff b =
    (-1 : LaurentPolynomial ℤ) ^ ℓ *
      (V ℓ).coeff (b - (-2 * ↑j * ↑ℓ + 2 * ↑(ℓ + ℓ.choose 2))) := by
  rw [neg_A_Q₀_pow, mul_assoc ((-A_hahn j) ^ ℓ), ← pow_add,
    neg_A_pow_mul_Q₀_pow_eq_single_general, coeff_single_mul_general]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
