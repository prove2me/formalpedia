-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tsum_coeff_congr_of_per_term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:28:57.042755+00:00
-- url     : https://prove2.me/submissions/49b5578e-0d90-4e75-9d0b-9f7c152f02b6

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_per_term_simplify

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (m : ℕ) : letI := piTop;
    (∑' k : ℕ, qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m =
    (∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
      qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) : R).coeff m := by
  letI := piTop
  congr 1
  exact tsum_congr (fun k => per_term_simplify x k)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
