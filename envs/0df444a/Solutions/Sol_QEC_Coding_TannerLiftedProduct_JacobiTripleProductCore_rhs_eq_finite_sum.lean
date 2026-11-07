-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.rhs_eq_finite_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:49:13.126186+00:00
-- url     : https://prove2.me/submissions/8ea93002-eed7-43de-bbc1-46242e265f25

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_product_term_coeff_vanishes
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summable_mul_series

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (m : ℕ) : letI := piTop;
    (∑' k : ℕ, qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m =
    ∑ k ∈ Finset.range (m + 1),
      (qPochhammerInf (q ^ 2) (q ^ 2) *
        (q ^ (k ^ 2) * x ^ k *
          PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m := by
  letI := piTop
  have hcomm := (summable_mul_series x).map_tsum
    (PowerSeries.coeff m : R →ₗ[_] _).toAddMonoidHom
    (PowerSeries.WithPiTopology.continuous_coeff _ m)
  simp only [LinearMap.toAddMonoidHom_coe] at hcomm
  rw [hcomm]
  exact tsum_eq_sum (fun k hk => product_term_coeff_vanishes x m k
    (by simp only [Finset.mem_range, not_lt] at hk; omega))
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
