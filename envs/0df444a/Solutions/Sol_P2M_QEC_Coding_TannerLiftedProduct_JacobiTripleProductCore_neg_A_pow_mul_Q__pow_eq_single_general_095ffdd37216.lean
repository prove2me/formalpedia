-- Prove2me | solution 1 for P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_pow_mul_Q__pow_eq_single_general_095ffdd37216
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:38:28.453678+00:00
-- url     : https://prove2.me/submissions/3929ae6c-0c6e-48e0-b179-71b6e924b1b2

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j ℓ n : ℕ) :
    (-A_hahn j) ^ ℓ * Q₀ ^ n =
    HahnSeries.single (-2 * ↑j * ↑ℓ + 2 * ↑n : ℤ) ((-1 : LaurentPolynomial ℤ) ^ ℓ) := by
  simp only [A_hahn, Q₀, ← HahnSeries.single_neg]
  rw [HahnSeries.single_pow, HahnSeries.single_pow, HahnSeries.single_mul_single]
  simp [mul_comm, mul_left_comm]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
