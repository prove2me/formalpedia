-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceSecondReadout.gradientInput_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:06:53.381779+00:00
-- url     : https://prove2.me/submissions/25e43256-a6ec-4dfb-9734-639622fdf20c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderCoboundary_squared
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xDelta1_decomposition
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_coboundary1_eq


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
theorem _root_.solution (x : P.X) (g : Word F (DoubleCylinderVertex P x witnessScale)) :
    (gradientInput x g).val=xFlow P witnessScale x
      (wordLinearMapTranspose (doubleCylinderBoundary1 P x witnessScale) g) := by
  change (indexedFamily witnessScale 3).coboundary1 rxIndex.succ (gradientError x g)=_
  rw [indexedFamily_coboundary1]
  change tannerCoboundary1 (rxReplacementPresentation P witnessScale)
    (xExtend P witnessScale x
      (wordLinearMapTranspose (doubleCylinderBoundary1 P x witnessScale) g))=_
  rw [rxPresentation_coboundary1_eq P (state witnessScale 2).admissible
    (state witnessScale 2).regular witnessScale]
  change BDL26ReplacementCochainMaps.rxCoboundary1 P witnessScale
    (xExtend P witnessScale x
      (wordLinearMapTranspose (doubleCylinderBoundary1 P x witnessScale) g))=_
  rw [xDelta1_decomposition]
  have hz : wordLinearMapTranspose (doubleCylinderBoundary2 P x witnessScale)
      (wordLinearMapTranspose (doubleCylinderBoundary1 P x witnessScale) g)=0 :=
    LinearMap.congr_fun (doubleCylinderCoboundary_squared P x witnessScale) g
  rw [hz,map_zero,zero_add]
end QEC.Coding.BDL26RXFaceSecondReadout
