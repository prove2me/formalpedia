-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceSecondReadout.gradientInput_old_z_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:29:04.427939+00:00
-- url     : https://prove2.me/submissions/a2287aaa-5f6f-43b1-bc40-747ed19b48fa

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
import Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_gradientInput_value
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xFlow_at_z


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
theorem _root_.solution (x : P.X)
    (g : Word F (DoubleCylinderVertex P x witnessScale)) (z : P.Z) (c : BDL26FiniteTannerSquare.Two) :
    (gradientInput x g).val (Sum.inr (z,c))=0 := by
  rw [gradientInput_value,xFlow_at_z]
end QEC.Coding.BDL26RXFaceSecondReadout
