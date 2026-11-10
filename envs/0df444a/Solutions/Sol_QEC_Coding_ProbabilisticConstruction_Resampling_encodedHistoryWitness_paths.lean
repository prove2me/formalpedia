-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.encodedHistoryWitness_paths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:22:13.678103+00:00
-- url     : https://prove2.me/submissions/f1b3e35d-d86a-43e8-8c6c-f5bd720ea7ac

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Mathlib.Data.Finset.Max
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPaths_pathsToTree

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (root : I) (L : List I) :
    witnessPaths G (L.length + 1) root (encodedHistoryWitness G root L) =
      historyWitness G root L :=
  witnessPaths_pathsToTree G _ _ _ _ _
end QEC.Coding.ProbabilisticConstruction.Resampling
