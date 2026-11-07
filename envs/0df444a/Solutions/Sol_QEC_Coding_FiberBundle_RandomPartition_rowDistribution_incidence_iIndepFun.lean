-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.rowDistribution_incidence_iIndepFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:28:50.137214+00:00
-- url     : https://prove2.me/submissions/0b12dad9-ae18-4ca5-a51f-dfb6f55b87ee

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowDistribution_variable_iIndepFun

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun b (row : RowSample r) => row b false)
      (rowDistribution r Delta hDelta).toMeasure := by
  exact
    (rowDistribution_variable_iIndepFun r Delta hDelta).comp
      (fun _b localSample => localSample false)
      (fun _b => Measurable.of_discrete)
end QEC.Coding.FiberBundle.RandomPartition
