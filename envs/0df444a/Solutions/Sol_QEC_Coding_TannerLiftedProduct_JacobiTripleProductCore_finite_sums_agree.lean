-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finite_sums_agree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:53:13.869943+00:00
-- url     : https://prove2.me/submissions/3e1aaf0b-a575-412a-8320-032270edd75e

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_lhs_term_vanishes_of_gt
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_termwise_coeff_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 1 + 1),
      (qBinom (q ^ 2) (2 * m + 1) k * (q ^ (k ^ 2) * x ^ k) : R).coeff m =
    ∑ k ∈ Finset.range (m + 1),
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m := by
  rw [show 2 * m + 1 + 1 = (m + 1) + (m + 1) by omega, Finset.sum_range_add]
  rw [Finset.sum_eq_zero fun k _ => lhs_term_vanishes_of_gt x m ((m + 1) + k) (by omega), add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  exact termwise_coeff_eq x m k (by omega)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
