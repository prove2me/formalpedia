-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.mul_tsum_eq_tsum_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:48:05.077325+00:00
-- url     : https://prove2.me/submissions/c5f61890-027a-47ad-a0b2-0eb0a70450c8

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_series_summable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_instIsTopologicalSemiringPiTop

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) : letI := piTop;
    (qPochhammerInf (q ^ 2) (q ^ 2) *
      (∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R) =
    (∑' k : ℕ, qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R) := by
  letI := piTop
  haveI := instIsTopologicalSemiringPiTop
  haveI : @T2Space R piTop := PowerSeries.WithPiTopology.instT2Space _
  exact ((series_summable x).tsum_mul_left _).symm
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
