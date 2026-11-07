-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_F_neg_reindexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:55:18.293963+00:00
-- url     : https://prove2.me/submissions/cfdc11cd-2156-4203-9b53-3ab67b07bf12

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_F_neg_finite_support

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piTop;
    Summable (fun p : ℕ × ℕ => F (-(↑p.1 + 1), p.2)) := by
  letI := piTop; rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]; intro d
  exact (coeff_F_neg_finite_support d).elim fun S_fin hS =>
    summable_of_ne_finset_zero (s := S_fin) fun p hp => hS p hp
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
