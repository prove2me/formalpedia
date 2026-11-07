-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summand_term_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:49:45.427914+00:00
-- url     : https://prove2.me/submissions/ab3b3183-93cd-4ee4-85a6-b3d0c6fa085d

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (k ℓ : ℕ) :
    q ^ (k ^ 2) * PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      ((-1 : R) ^ ℓ * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      ((-1 : R) ^ ℓ * q ^ ((k + ℓ) ^ 2 + ℓ)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 := by
  rw [show q ^ (k ^ 2) * PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      ((-1 : R) ^ ℓ * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
      PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      ((-1 : R) ^ ℓ * (q ^ (k ^ 2) * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ))) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 by ring_nf,
    show q ^ (k ^ 2) * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) = q ^ ((k + ℓ) ^ 2 + ℓ) by
      rw [← pow_add]
      congr 1
      ring]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
