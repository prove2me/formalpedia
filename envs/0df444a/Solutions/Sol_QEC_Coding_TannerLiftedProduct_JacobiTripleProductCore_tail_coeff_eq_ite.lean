-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tail_coeff_eq_ite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:46:00.033503+00:00
-- url     : https://prove2.me/submissions/98c3347e-60d6-4df7-9366-6c191667be77

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tail_factor_delta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_prod_coeff_delta

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (m n k : ℕ) (hmn : m < n) (j : ℕ) (hj : j ≤ m) :
    (qPoch ((-x * q) * (q ^ 2) ^ n) (q ^ 2) k : R).coeff j =
    if j = 0 then 1 else 0 := by
  unfold qPoch
  exact prod_coeff_delta m (fun i => 1 - ((-x * q) * (q ^ 2) ^ n) * (q ^ 2) ^ i) k
    (fun i _hi j hj => tail_factor_delta x m n hmn i j hj) j hj
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
