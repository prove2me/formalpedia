-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.localDistribution_coordinate_iIndepFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:28:47.027072+00:00
-- url     : https://prove2.me/submissions/76a9287c-4954-4267-82e3-8b8f37a0fd23

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_iIndepFun


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun side (localSample : LocalSample) => localSample side)
      (localDistribution r Delta hDelta).toMeasure := by
  exact RandomBase.independentProduct_iIndepFun _
end QEC.Coding.FiberBundle.RandomPartition
