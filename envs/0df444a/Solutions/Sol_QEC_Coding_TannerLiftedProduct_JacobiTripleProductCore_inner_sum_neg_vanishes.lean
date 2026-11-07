-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.inner_sum_neg_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:03:17.480207+00:00
-- url     : https://prove2.me/submissions/6a36be03-fb09-4535-a62e-72a751119fc4

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_instIsTopologicalSemiringPiTop
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_G_summable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tsum_G_eq_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j : ℕ) : letI := piTop;
    ∑' ℓ : ℕ, F (-(↑j + 1), ℓ) = 0 := by
  letI : TopologicalSpace R := piTop
  haveI : T2Space R := PowerSeries.WithPiTopology.instT2Space _
  haveI := instIsTopologicalSemiringPiTop
  have heq : (fun ℓ : ℕ => F (-(↑j + 1), ℓ)) = (fun ℓ : ℕ =>
      PowerSeries.C (LaurentPolynomial.T (-(↑j + 1))) *
      ((-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1)) := by
    ext ℓ
    simp only [F, mul_assoc]
  rw [heq, (G_summable j).tsum_mul_left, tsum_G_eq_zero j, mul_zero]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
