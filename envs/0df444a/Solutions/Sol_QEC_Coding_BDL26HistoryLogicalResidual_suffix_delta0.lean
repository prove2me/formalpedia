-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.suffix_delta0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:04:10.300319+00:00
-- url     : https://prove2.me/submissions/0a64cb63-5a9b-4ffc-a4db-684d38810088

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
    (SuffixData S n).family.coboundary0 i =
      tannerCoboundary0 (state S (i.val+2)).presentation := by
  change (indexedFamily S (n+2)).coboundary0 (LevelTwoHistory.physicalLevel i) = _
  exact indexedFamily_coboundary0 S (n+2) (LevelTwoHistory.physicalLevel i)
end QEC.Coding.BDL26HistoryLogicalResidual
