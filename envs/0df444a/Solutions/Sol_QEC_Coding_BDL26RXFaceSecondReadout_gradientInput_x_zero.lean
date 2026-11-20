-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceSecondReadout.gradientInput_x_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:25:17.565337+00:00
-- url     : https://prove2.me/submissions/52748cd6-731b-43dc-9857-c355532324eb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
import Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_gradientInput_value
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xFlow_at_x


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
theorem _root_.solution (x y : P.X)
    (g : Word F (DoubleCylinderVertex P x witnessScale)) :
    restrictWordLinear (Lx.syndromeRegion y) (gradientInput x g).val=0 := by
  funext j
  obtain ⟨face,rfl⟩ := (xSyndromeEquiv P witnessScale y).surjective j
  change (gradientInput x g).val (Sum.inl (Sum.inl ⟨y,face⟩))=0
  rw [gradientInput_value,xFlow_at_x]
end QEC.Coding.BDL26RXFaceSecondReadout
