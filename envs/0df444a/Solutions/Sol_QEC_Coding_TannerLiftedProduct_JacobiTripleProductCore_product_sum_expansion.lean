-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.product_sum_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:59:47.602376+00:00
-- url     : https://prove2.me/submissions/cf288bde-3aae-4224-9fc5-8eb052c2e369

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_product_sum_expansion_coeff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) : letI := piTop;
    qPochhammerInf (q ^ 2) (q ^ 2) * qPochhammerInf (-x * q) (q ^ 2) =
    ∑' k : ℕ, q ^ (k ^ 2) * x ^ k * qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) :=
  PowerSeries.ext fun m => product_sum_expansion_coeff x m
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
