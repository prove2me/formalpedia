-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceSecondReadout.gradientInput_root_forced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:20:45.951177+00:00
-- url     : https://prove2.me/submissions/b47d5a03-fd93-41fc-a88f-8da25518bf0e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
import Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_selectedQWord_forced
import Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_gradientInput_q

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
    (hxq : P.xq x q=true) (b : F)
    (hg : rxXQDegreeZero P (state witnessScale 2).admissible.toTannerSquareAdmissible
      q x hxq witnessScale g=qPortWord P q b) :
    selectedQWord (gradientInput x g) q (0,Sum.inl (Sum.inl ()))=b := by
  apply selectedQWord_forced
  rw [gradientInput_q x g q hxq,hg]
end QEC.Coding.BDL26RXFaceSecondReadout
