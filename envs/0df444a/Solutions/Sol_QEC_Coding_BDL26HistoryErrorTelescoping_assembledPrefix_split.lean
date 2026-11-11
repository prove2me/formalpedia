-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.assembledPrefix_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:41:33.571715+00:00
-- url     : https://prove2.me/submissions/78407651-d08b-4937-bf3f-b11f1871e2a6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_historyPrefixSum_split

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
theorem _root_.solution (sigma : TopInput S n) (a b : LevelIndex n)
    (hab : a.val ≤ b.val) :
    assembledPrefix S n sigma b = correctionIntervalSum S n sigma a b +
      intervalMap1 (SuffixData S n) a b hab (assembledPrefix S n sigma a) :=
  historyPrefixSum_split _ _ a b hab
end QEC.Coding.BDL26HistoryErrorTelescoping
