-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.rowDistribution_incidence_hasLaw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:28:50.993571+00:00
-- url     : https://prove2.me/submissions/a5c9c92a-29ac-4629-a94b-b624a706412f

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowDistribution_variable_hasLaw
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_localDistribution_coordinate_hasLaw

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) :
    ProbabilityTheory.HasLaw
      (fun row : RowSample r => row b false)
      (PMF.bernoulli
        (RandomBase.incidenceProbability (4 * r) Delta)
        (RandomBase.incidenceProbability_le_one hDelta)).toMeasure
      (rowDistribution r Delta hDelta).toMeasure := by
  have hLocal :=
    localDistribution_coordinate_hasLaw r Delta hDelta false
  have hVariable :=
    rowDistribution_variable_hasLaw r Delta hDelta b
  exact hLocal.comp hVariable
end QEC.Coding.FiberBundle.RandomPartition
