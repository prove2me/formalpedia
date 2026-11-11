-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.suffixEquiv_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:23:10.367778+00:00
-- url     : https://prove2.me/submissions/97346503-a853-486e-a12e-5f9333860cc8

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
theorem _root_.solution (a : LevelIndex n) (x : FC.H1 S (a.val+2)) :
    suffixEquiv S n a a x = x := (FC.prefixEquiv S (a.val+2)).apply_symm_apply x
end QEC.Coding.BDL26HistoryLogicalResidual
