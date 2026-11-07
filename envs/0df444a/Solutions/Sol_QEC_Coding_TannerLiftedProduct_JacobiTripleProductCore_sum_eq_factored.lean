-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.sum_eq_factored
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:53:40.284224+00:00
-- url     : https://prove2.me/submissions/bb861af8-f698-425e-9cea-774083af013e

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summand_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_antidiag_to_range_sum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution {n : ℕ} :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, aCoeff p.1 * bCoeff p.2 =
    (-1) ^ n * PowerSeries.invOfUnit (P n) 1 *
    ∑ k ∈ Finset.range (n + 1),
      qBinom (q ^ 2) n k * (-(1 : R)) ^ k * (q ^ 2) ^ k.choose 2 := by
  rw [antidiag_to_range_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  exact summand_eq (by simp only [Finset.mem_range] at hk; omega)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
