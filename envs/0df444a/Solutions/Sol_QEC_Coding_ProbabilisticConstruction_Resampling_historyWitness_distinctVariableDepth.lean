-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.historyWitness_distinctVariableDepth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:23:29.447901+00:00
-- url     : https://prove2.me/submissions/f9f7d2c4-2f65-4d5d-95bb-b8408f995d2a

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_historyWitness_shared_depth_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (root : I) (L : List I) :
    DistinctVariableDepth vars root (historyWitness (supportGraph vars) root L) := by
  intro p hp q hq v hpv hqv hd
  exact historyWitness_shared_depth_injective vars root L p q hp hq v hpv hqv hd
end QEC.Coding.ProbabilisticConstruction.Resampling
