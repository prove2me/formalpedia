-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.rowViolation_measureReal_ge_exp_of_Delta_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:50:10.834949+00:00
-- url     : https://prove2.me/submissions/47aa8262-0d3a-4b7c-ac66-09f6bdf63ec1

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_incidenceProbability_toReal_le_half
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowViolation_measureReal_ge_exp

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta : Nat) (hDeltaHalf : Delta ≤ 2 * r)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    (1 -
      Real.exp
        (-(RandomBase.incidenceProbability (4 * r) Delta).toReal *
          ((HammingWeight y : Real) + HammingWeight z))) / 2 ≤
      (rowDistribution r Delta (by omega)).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0} := by
  exact rowViolation_measureReal_ge_exp r Delta (by omega) y z
    (incidenceProbability_toReal_le_half r Delta hDeltaHalf)
end QEC.Coding.FiberBundle.RandomPartition
