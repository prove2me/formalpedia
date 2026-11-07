-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tsum_F_neg_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:06:00.768177+00:00
-- url     : https://prove2.me/submissions/84a83dc9-d6a7-44a3-9be1-17019536bde1

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tsum_F_neg_NxN_eq_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piTop;
    (∑' (p : {p : ℤ × ℕ // ¬(0 ≤ p.1)}), F p.val) = 0 := by
  letI := piTop
  rw [← Equiv.tsum_eq negReindex]
  simp only [negReindex, Equiv.coe_fn_mk]
  exact tsum_F_neg_NxN_eq_zero
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
