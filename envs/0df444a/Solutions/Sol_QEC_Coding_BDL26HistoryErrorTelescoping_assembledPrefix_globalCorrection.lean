-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.assembledPrefix_globalCorrection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:09:56.036181+00:00
-- url     : https://prove2.me/submissions/29220e84-0395-4d40-8beb-4211fab0817f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_assembledPrefix_top
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_historyLiftedCorrection_eq_globalCorrection


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
theorem _root_.solution (sigma : TopInput S n) :
    assembledPrefix S n sigma (TopIndex n) =
      globalCorrection (SuffixData S n)
        (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) (actualBase S n) sigma := by
  rw [assembledPrefix_top]
  exact historyLiftedCorrection_eq_globalCorrection _ _ _ _
end QEC.Coding.BDL26HistoryErrorTelescoping
