-- Prove2me | solution 1 for P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_pow_mul_Q__pow_eq_single_f8efc88f6b2b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:15:06.118714+00:00
-- url     : https://prove2.me/submissions/434af734-cfe5-4a71-b936-c38af0deff0f

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j ℓ : ℕ) :
    (-A_hahn j) ^ ℓ * Q₀ ^ (ℓ.choose 2) =
    HahnSeries.single (-2 * ↑j * ↑ℓ + 2 * ↑(ℓ.choose 2) : ℤ) ((-1 : LaurentPolynomial ℤ) ^ ℓ) := by
  simp only [A_hahn, Q₀, ← HahnSeries.single_neg]
  rw [HahnSeries.single_pow, HahnSeries.single_pow, HahnSeries.single_mul_single]
  simp [mul_comm, mul_left_comm]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
