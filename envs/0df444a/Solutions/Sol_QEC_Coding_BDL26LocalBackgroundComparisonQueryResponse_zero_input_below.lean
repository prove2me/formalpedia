-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.zero_input_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:38:31.377363+00:00
-- url     : https://prove2.me/submissions/cd3819fa-6f7f-4b0a-983f-a7df8c5c0267

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonQueryResponse
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_top
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_actual_interval_contraction


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual (suffix_delta1)
open BDL26LocalBackgroundComparisonResponse BDL26PairedHistoryQueryCone
open MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
theorem _root_.solution (s : TopInput S n) (hs : s.val = 0) (a : LevelIndex n) :
    (actualInputs S n s a).val = 0 := by
  have hc := actual_interval_contraction S n s a (TopIndex n) (Nat.le_of_lt_succ a.isLt)
  rw [actualInputs_top,hs,HammingWeight_zero] at hc
  apply (HammingWeight_eq_zero_iff _).mp
  have hp : 0 < 2 ^ rxCount a.val n := by positivity
  nlinarith
end QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
