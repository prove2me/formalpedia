-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.conv_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:37:59.49556+00:00
-- url     : https://prove2.me/submissions/3a3bff7e-d868-49f3-b27f-e95e1bc17470

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_qpow_mul_xpow_ge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_qBinom_eq_coeff_inv_on_antidiag

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (m k : ℕ) (hk : k ≤ m) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
      (qBinom (q ^ 2) (2 * m + 1) k : R).coeff p.1 * (q ^ (k ^ 2) * x ^ k).coeff p.2 =
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
      (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff p.1 *
      (q ^ (k ^ 2) * x ^ k).coeff p.2 := by
  apply Finset.sum_congr rfl
  intro ⟨i, j⟩ hij
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  by_cases hj : k ^ 2 ≤ j
  · congr 1
    exact coeff_qBinom_eq_coeff_inv_on_antidiag m k i j hk hij hj
  · push_neg at hj
    rw [PowerSeries.coeff_of_lt_order j (lt_of_lt_of_le (by exact_mod_cast hj)
      (order_qpow_mul_xpow_ge x k)), mul_zero, mul_zero]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
