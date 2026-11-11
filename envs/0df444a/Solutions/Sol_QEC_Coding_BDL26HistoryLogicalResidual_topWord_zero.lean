-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.topWord_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:52:03.66777+00:00
-- url     : https://prove2.me/submissions/97c52b32-35dd-41b1-925d-6970bc49820a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_topWord_of_closed

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (sigma : TopInput S n) : topWord S n sigma 0 = 0 :=
  topWord_of_closed S n sigma 0 (map_zero _)
end QEC.Coding.BDL26HistoryLogicalResidual
