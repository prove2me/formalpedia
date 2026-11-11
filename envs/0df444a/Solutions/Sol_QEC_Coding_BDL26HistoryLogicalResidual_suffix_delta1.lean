-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.suffix_delta1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:04:07.091408+00:00
-- url     : https://prove2.me/submissions/304d1cce-416b-47fb-9d24-7a8393d07cf6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (i : LevelIndex n) :
    (SuffixData S n).family.coboundary1 i =
      tannerCoboundary1 (state S (i.val+2)).presentation := by
  change (indexedFamily S (n+2)).coboundary1 (LevelTwoHistory.physicalLevel i) = _
  exact indexedFamily_coboundary1 S (n+2) (LevelTwoHistory.physicalLevel i)
end QEC.Coding.BDL26HistoryLogicalResidual
