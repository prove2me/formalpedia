-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.actualHistory_through
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:42:23.701192+00:00
-- url     : https://prove2.me/submissions/93c398d2-43f3-4a68-9eee-bcdbbd6a8035

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_prefixHistory_through
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_prefixHistory_top_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26DecodingGraph
open scoped Classical
universe u v
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (sigma : TopInput S n) (b : LevelIndex n) :
    historyThrough (SuffixData S n) (actualHistory S n sigma) b =
      prefixHistory (SuffixData S n)
        (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) (actualBase S n)
        b.val (Nat.le_of_lt_succ b.isLt) (actualInputs S n sigma b) := by
  change historyThrough (SuffixData S n) (buildCorrectionHistory _ _ _ sigma) b = _
  have hh := prefixHistory_top_eq (SuffixData S n)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) (actualBase S n) sigma
  rw [← hh]
  exact prefixHistory_through (SuffixData S n)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) (actualBase S n)
    n (Nat.le_refl _) sigma b (Nat.le_of_lt_succ b.isLt)
end QEC.Coding.BDL26HistoryErrorTelescoping
