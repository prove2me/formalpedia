-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_single_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:40:00.062739+00:00
-- url     : https://prove2.me/submissions/6b1834f3-3b28-4ab1-a0f7-2fb58fb8c31c

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j d : ℕ) (tail : S_hahn) :
    (HahnSeries.single ((j + 1 : ℤ) ^ 2) (1 : LaurentPolynomial ℤ) * tail).coeff (↑d) =
    tail.coeff ((d : ℤ) - (j + 1 : ℤ) ^ 2) := by
  conv_lhs => rw [show (d : ℤ) = ((d : ℤ) - (j + 1 : ℤ) ^ 2) + (j + 1 : ℤ) ^ 2 by ring]
  rw [HahnSeries.coeff_single_mul_add, one_mul]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
