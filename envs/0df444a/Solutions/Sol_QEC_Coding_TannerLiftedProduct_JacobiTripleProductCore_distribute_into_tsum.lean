-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.distribute_into_tsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:53:46.409203+00:00
-- url     : https://prove2.me/submissions/8c07edad-9407-4899-88f5-c080f4136cfe

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_instIsTopologicalSemiringPiTop
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_piTop_T3
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_inner_series_summable

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (k : ℕ) : letI := piTop;
    q ^ (k ^ 2) * PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      (∑' ℓ : ℕ, (-1 : R) ^ ℓ * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    ∑' ℓ : ℕ,
      q ^ (k ^ 2) * PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      ((-1 : R) ^ ℓ * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) := by
  letI := piTop
  haveI : T3Space R := piTop_T3
  haveI : IsTopologicalSemiring R := instIsTopologicalSemiringPiTop
  rw [(inner_series_summable k).tsum_mul_left]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
