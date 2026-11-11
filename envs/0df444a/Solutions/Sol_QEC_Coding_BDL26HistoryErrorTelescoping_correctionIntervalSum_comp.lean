-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.correctionIntervalSum_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:43:58.850495+00:00
-- url     : https://prove2.me/submissions/06e3148e-c208-497b-a8e9-373e8e862515

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_historyIntervalSum_comp

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
theorem _root_.solution (sigma : TopInput S n) (a b c : LevelIndex n)
    (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val) :
    correctionIntervalSum S n sigma a c =
      intervalMap1 (SuffixData S n) b c hbc (correctionIntervalSum S n sigma a b) +
        correctionIntervalSum S n sigma b c :=
  historyIntervalSum_comp _ _ a b c hab hbc
end QEC.Coding.BDL26HistoryErrorTelescoping
