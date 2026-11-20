-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceSecondReadout.physicalReadout_one_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:42:57.79318+00:00
-- url     : https://prove2.me/submissions/567ffc47-ffad-4220-9fb7-ff51efbb795c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
import Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_physicalReadout_one
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_zero_run_coarse
import Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_zero_run_coarse


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFaceSecondReadout
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26RXDecoderAdapter
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXFaceSecondReadout
theorem _root_.solution (S : OddScale) : physicalReadout S 1 0=0 := by
  rw [physicalReadout_one]
  exact BDL26RXErrorPullback.zero_run_coarse S 3 rxIndex rxIndex_even
end QEC.Coding.BDL26RXFaceSecondReadout
