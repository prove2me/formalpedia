-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.variableRank_eq_historyCounter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:24:35.470406+00:00
-- url     : https://prove2.me/submissions/697baddf-753e-4e44-a7bd-63d63e67cde5

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryCounters
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_earlier_nodes_card_eq_rank
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_earlier_nodes_card_eq_counter

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (root : I) (L : List I) (p : List I × ℕ)
    (hp : p ∈ timedHistoryWitness (supportGraph vars) root 0 L)
    (v : V) (hpv : v ∈ vars (pathLabel root p.1)) :
    variableRank vars root (historyWitness (supportGraph vars) root L) p.1 v =
      historyCounter vars root L p.2 v :=
  (earlier_nodes_card_eq_rank vars root L p hp v hpv).symm.trans
    (earlier_nodes_card_eq_counter vars root L p hp v hpv)
end QEC.Coding.ProbabilisticConstruction.Resampling
