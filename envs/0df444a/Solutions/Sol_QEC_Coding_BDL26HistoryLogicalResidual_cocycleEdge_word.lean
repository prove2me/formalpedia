-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.cocycleEdge_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:56:36.988021+00:00
-- url     : https://prove2.me/submissions/112cb5ba-3497-43eb-9255-c839a5d53366

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_selectedMap_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (i : StepIndex n) (w : FC.Cocycle S (i.castSucc.val+2)) :
    (cocycleEdge S n i w).val = ((SuffixData S n).selectedMap i).map1 w.val := by
  rw [LevelTwoHistory.suffix_selected_map1,selectedMap_eq]
  exact FC.stepCocycle_value S (i.val+2) w
end QEC.Coding.BDL26HistoryLogicalResidual
