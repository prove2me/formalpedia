-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.rowDistribution_variable_iIndepFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:20:18.099206+00:00
-- url     : https://prove2.me/submissions/05daf0fd-f604-4117-8861-742e8c5cc7fe

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
      (fun b (row : RowSample r) => row b)
      (rowDistribution r Delta hDelta).toMeasure := by
  exact RandomBase.independentProduct_iIndepFun _
end QEC.Coding.FiberBundle.RandomPartition
