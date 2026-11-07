-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.sum_interchange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:38:04.311891+00:00
-- url     : https://prove2.me/submissions/1d9f2d58-c5c4-4eac-b403-527547a61f5c

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summable_F

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piTop;
    (∑' k : ℕ, ∑' ℓ : ℕ,
      PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      ((-1 : R) ^ ℓ * q ^ ((k + ℓ) ^ 2 + ℓ)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    ∑' p : ℕ × ℕ,
      PowerSeries.C (LaurentPolynomial.T (p.1 : ℤ)) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1 := by
  letI : UniformSpace R := piUnif
  haveI : IsUniformAddGroup R := PowerSeries.WithPiTopology.instIsUniformAddGroup _
  haveI : CompleteSpace R := PowerSeries.WithPiTopology.instCompleteSpace _
  haveI : T0Space R := PowerSeries.WithPiTopology.instT0Space _
  exact summable_F.tsum_prod.symm
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
