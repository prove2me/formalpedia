-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.AB_eq_one_in_S
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:38:00.363543+00:00
-- url     : https://prove2.me/submissions/207740f5-a607-4e01-af8c-b54c457a9d05

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_tsum_CS_mul_t_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_convolution_eq_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : A_S * B_S = 1 := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one]
  simp_rw [show ∀ n, @PowerSeries.coeff R _ n A_S = aCoeff n from coeff_tsum_CS_mul_t_pow aCoeff,
    show ∀ n, @PowerSeries.coeff R _ n B_S = bCoeff n from coeff_tsum_CS_mul_t_pow bCoeff]
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp [Finset.Nat.antidiagonal_zero, aCoeff, bCoeff, P, qPoch,
      show PowerSeries.invOfUnit (1 : R) 1 = 1 by
        have := PowerSeries.invOfUnit_mul (1 : R) 1 (by simp)
        rwa [mul_one] at this]
  · rw [if_neg (by omega), convolution_eq_zero hn]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
