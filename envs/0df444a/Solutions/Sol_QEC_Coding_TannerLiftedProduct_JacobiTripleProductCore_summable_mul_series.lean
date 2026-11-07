-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_mul_series
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:47:47.019634+00:00
-- url     : https://prove2.me/submissions/1f30efea-fcbe-433b-b8cc-5911ddcd899c

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
    Summable fun k : ℕ => qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) := by
  letI := piTop
  haveI := instIsTopologicalSemiringPiTop
  exact (series_summable x).mul_left _
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
