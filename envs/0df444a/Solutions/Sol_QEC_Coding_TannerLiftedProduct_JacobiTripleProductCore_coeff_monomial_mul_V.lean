-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_monomial_mul_V
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:38:27.522159+00:00
-- url     : https://prove2.me/submissions/0735065c-fc23-4305-91be-7deff8747b90

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_pow_mul_Q__pow_eq_single_f8efc88f6b2b

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j ℓ : ℕ) (b : ℤ) :
    ((-A_hahn j) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ).coeff b =
    (-1 : LaurentPolynomial ℤ) ^ ℓ * (V ℓ).coeff (b - (-2 * ↑j * ↑ℓ + 2 * ↑(ℓ.choose 2))) := by
  set e := -2 * (j : ℤ) * ↑ℓ + 2 * ↑(ℓ.choose 2)
  rw [neg_A_pow_mul_Q₀_pow_eq_single]
  conv_lhs => rw [show b = (b - e) + e by ring]
  exact HahnSeries.coeff_single_mul_add
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
