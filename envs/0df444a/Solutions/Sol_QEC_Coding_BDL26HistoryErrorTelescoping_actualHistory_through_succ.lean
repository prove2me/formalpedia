-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.actualHistory_through_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:48:55.178212+00:00
-- url     : https://prove2.me/submissions/5f5f13a4-7981-4b5e-9dbf-94f36df5144b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_prefixHistory_step_eq
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actualOutput_coarse
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actualHistory_through

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
theorem _root_.solution (sigma : TopInput S n) (i : StepIndex n) :
    historyThrough (SuffixData S n) (actualHistory S n sigma) i.succ =
      .step i (actualOutput S n sigma i) ::
        historyThrough (SuffixData S n) (actualHistory S n sigma) i.castSucc := by
  rw [actualHistory_through,actualHistory_through]
  have hs := actualOutput_coarse S n sigma i
  rw [← hs]
  change prefixHistory (SuffixData S n)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) (actualBase S n)
    (i.val+1) (by have := i.isLt; omega) (actualInputs S n sigma i.succ) = _
  rw [prefixHistory_step_eq] <;> rfl
end QEC.Coding.BDL26HistoryErrorTelescoping
