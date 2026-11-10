-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.historyWitness_ne_of_root_count_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:24:25.484837+00:00
-- url     : https://prove2.me/submissions/1eaa2686-3be8-4e97-9526-c31d3b2c3a96

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Mathlib.Data.Finset.Max
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_historyWitness_root_count

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (root : I) (L K : List I)
    (h : L.count root ≠ K.count root) : historyWitness G root L ≠ historyWitness G root K := by
  intro he
  have hc := congrArg (labelCount root root) he
  rw [historyWitness_root_count, historyWitness_root_count] at hc
  exact h (Nat.add_right_cancel hc)
end QEC.Coding.ProbabilisticConstruction.Resampling
