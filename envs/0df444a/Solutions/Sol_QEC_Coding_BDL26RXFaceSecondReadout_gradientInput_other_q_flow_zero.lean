-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceSecondReadout.gradientInput_other_q_flow_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:43:04.632417+00:00
-- url     : https://prove2.me/submissions/60fd8e13-e9fc-43e7-905e-4e36a6c0dce5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
import Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_zero_x_cleaned_input
import Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_selectedQWord_flow_zero
import Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_gradientInput_value
import Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_gradientInput_x_zero
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xFlow_at_q


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
    (g : Word F (DoubleCylinderVertex P x witnessScale)) (q : P.Q)
    (hxq : P.xq x q≠true) :
    qFlow P witnessScale q (selectedQWord (gradientInput x g) q)=0 := by
  apply selectedQWord_flow_zero
  rw [zero_x_cleaned_input (gradientInput x g) (gradientInput_x_zero x · g)]
  funext j
  obtain ⟨edge,rfl⟩ := (qSyndromeEquiv P witnessScale q).surjective j
  change (gradientInput x g).val (Sum.inl (Sum.inr ⟨q,edge⟩))=0
  rw [gradientInput_value,xFlow_at_q P
    (state witnessScale 2).admissible.toTannerSquareAdmissible,dif_neg hxq]
end QEC.Coding.BDL26RXFaceSecondReadout
