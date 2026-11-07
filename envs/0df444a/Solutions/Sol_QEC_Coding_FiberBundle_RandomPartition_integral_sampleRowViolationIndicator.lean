-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.integral_sampleRowViolationIndicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:33:16.115894+00:00
-- url     : https://prove2.me/submissions/b89af973-e1e9-482e-81b1-71c1bb38d885

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_distribution_row_hasLaw
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_integral_rowViolationIndicator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r)) :
    ∫ sample, sampleRowViolationIndicator y z a sample ∂
        (distribution r Delta hDelta).toMeasure =
      (rowDistribution r Delta hDelta).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0} := by
  calc
    _ =
        ∫ row, rowViolationIndicator y z row ∂
          (rowDistribution r Delta hDelta).toMeasure := by
      exact
        (distribution_row_hasLaw r Delta hDelta a).integral_comp
          ((Measurable.of_discrete :
            Measurable (rowViolationIndicator y z)).aestronglyMeasurable)
    _ = _ := integral_rowViolationIndicator r Delta hDelta y z
end QEC.Coding.FiberBundle.RandomPartition
