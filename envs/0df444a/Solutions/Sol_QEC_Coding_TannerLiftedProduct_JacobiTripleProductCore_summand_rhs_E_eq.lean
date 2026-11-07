-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summand_rhs_E_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:52:08.115269+00:00
-- url     : https://prove2.me/submissions/cba83455-a3c9-4cf2-9400-11493f12b902

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (m : ℤ) (ℓ : ℕ) :
    (PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2) *
    ((-(q * aI)) ^ ℓ * PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    PowerSeries.C (LaurentPolynomial.T (m - ↑ℓ)) *
    ((-1 : R) ^ ℓ * q ^ (m.natAbs ^ 2 + ℓ)) *
    PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 := by
  have h1 : (-(q * aI)) ^ ℓ = (-1 : R) ^ ℓ * q ^ ℓ *
      PowerSeries.C (LaurentPolynomial.T (-(ℓ : ℤ))) := by
    calc (-(q * aI)) ^ ℓ
        = (-1) ^ ℓ * (q ^ ℓ * aI ^ ℓ) := by rw [neg_pow, mul_pow]
      _ = (-1) ^ ℓ * (q ^ ℓ * PowerSeries.C (LaurentPolynomial.T (-1) ^ ℓ)) := by rw [map_pow]
      _ = _ := by rw [LaurentPolynomial.T_pow]; ring_nf
  have h2 : (PowerSeries.C (R := LaurentPolynomial ℤ)) (LaurentPolynomial.T m) *
      (PowerSeries.C (R := LaurentPolynomial ℤ)) (LaurentPolynomial.T (-(ℓ : ℤ))) =
      (PowerSeries.C (R := LaurentPolynomial ℤ)) (LaurentPolynomial.T (m - ↑ℓ)) := by
    rw [← map_mul, ← LaurentPolynomial.T_add]
    ring_nf
  rw [h1, pow_add, ← h2]
  ring
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
