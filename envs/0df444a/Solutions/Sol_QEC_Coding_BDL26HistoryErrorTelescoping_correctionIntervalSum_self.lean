-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.correctionIntervalSum_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:34:16.796642+00:00
-- url     : https://prove2.me/submissions/9dc6c966-38dd-48c5-9f69-87fe12e54c36

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_historyIntervalSum_self

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
theorem _root_.solution (sigma : TopInput S n) (a : LevelIndex n) :
    correctionIntervalSum S n sigma a a = 0 := historyIntervalSum_self _ _ a
end QEC.Coding.BDL26HistoryErrorTelescoping
