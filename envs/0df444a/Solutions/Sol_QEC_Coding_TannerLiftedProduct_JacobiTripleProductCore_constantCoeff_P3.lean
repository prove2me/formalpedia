-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.constantCoeff_P3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:55:26.698191+00:00
-- url     : https://prove2.me/submissions/6191a2d0-d83e-4da2-b415-b1977fcf17b7

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_multipliable_P3_factors

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piTop;
    (qPochhammerInf (-q * aI) (q ^ 2) : R).constantCoeff = 1 := by
  letI := piTop
  haveI : T2Space R := PowerSeries.WithPiTopology.instT2Space _
  unfold qPochhammerInf
  rw [tprod_eq_of_multipliable_unconditional multipliable_P3_factors]
  have := multipliable_P3_factors.map_tprod
    (PowerSeries.constantCoeff (R := LaurentPolynomial ℤ)).toMonoidHom
    (PowerSeries.WithPiTopology.continuous_constantCoeff _)
  simp only [MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe] at this
  rw [this]
  simp only [map_sub, map_one, map_mul, map_neg, map_pow,
    PowerSeries.constantCoeff_X, neg_zero, zero_mul, sub_zero]
  exact tprod_one
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
