-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tsum_F_neg_NxN_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:04:44.242202+00:00
-- url     : https://prove2.me/submissions/f3649a47-7bff-44ac-bd63-5743035d6808

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_instIsTopologicalSemiringPiTop
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_piTop_T3
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_inner_sum_summable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_inner_sum_neg_vanishes
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summable_F_neg_reindexed

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piTop;
    (∑' (c : ℕ × ℕ), F (-(↑c.1 + 1), c.2)) = 0 := by
  letI := piTop
  haveI := instIsTopologicalSemiringPiTop
  haveI := piTop_T3
  rw [show (fun c : ℕ × ℕ => F (-(↑c.1 + 1), c.2)) = fun c =>
      F (-(↑c.1 + 1 : ℤ), c.2) from rfl,
    @Summable.tsum_prod' R ℕ ℕ _ piTop _ _ _ summable_F_neg_reindexed inner_sum_summable]
  simp only [inner_sum_neg_vanishes, tsum_zero]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
