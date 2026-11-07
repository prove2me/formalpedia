-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.convolution_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:28:54.315772+00:00
-- url     : https://prove2.me/submissions/8ba8d7e9-138b-416b-9f57-c6f95da34335

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qBinom_theorem
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_one_eq_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_sum_eq_factored

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution {n : ℕ} (hn : 0 < n) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      aCoeff p.1 * bCoeff p.2 = 0 := by
  rw [sum_eq_factored, show ∑ k ∈ Finset.range (n + 1),
      qBinom (q ^ 2) n k * (-(1 : R)) ^ k * (q ^ 2) ^ k.choose 2 = qPoch 1 (q ^ 2) n
      from (qBinom_theorem 1 (q ^ 2) n).symm,
    qPoch_one_eq_zero _ hn, mul_zero]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
