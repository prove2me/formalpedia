-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonResponse.zero_seed_readout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:24:57.877409+00:00
-- url     : https://prove2.me/submissions/1a721f88-31c9-4218-bd6c-7dae350a335f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_StoppedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_readout
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actualHistory_zero_readout


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonResponse
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual
open scoped Classical BigOperators
namespace QEC.Coding.BDL26LocalBackgroundComparisonResponse
theorem _root_.solution (S : OddScale) (n : Nat) :
    BDL26AllDepthBottomComparisonStability.baseReadout S n
      (BDL26NonzeroBackgroundComparisonStability.zeroInput S n)=0 := by
  unfold BDL26AllDepthBottomComparisonStability.baseReadout
  rw [← actualInputs_readout]
  exact BDL26UniformRXTail.actualHistory_zero_readout S n
    (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) rfl
    (LevelTwoHistory.physicalLevel (0 : LevelIndex n))
end QEC.Coding.BDL26LocalBackgroundComparisonResponse
