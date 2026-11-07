-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tsum_F_eq_tsum_G
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:07:38.986113+00:00
-- url     : https://prove2.me/submissions/28ec5ae7-d6b9-449e-8f5e-dcf434ac87aa

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tsum_F_nonneg_eq_tsum_G
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tsum_F_neg_eq_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tsum_F_split

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piTop;
    (∑' p : ℤ × ℕ, F p) = (∑' p : ℕ × ℕ, G p) := by
  letI := piTop
  rw [tsum_F_split, tsum_F_nonneg_eq_tsum_G, tsum_F_neg_eq_zero]
  ring
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
