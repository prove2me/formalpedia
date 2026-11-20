-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceSecondReadout.exists_first_zero_second_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:26:13.585199+00:00
-- url     : https://prove2.me/submissions/3e374c77-0253-486f-8a9f-6deec96bcf93

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
import Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_physical_crossing
import Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_physicalReadout_one_zero
import Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_gradientError_tower_support
import Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_rectangle_physical_readout_nonzero

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
theorem _root_.solution :
    ∃ (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) (q : Physical S (n+2)),
      Nonempty (BDL26RXFaceEdgeTower.Tower S n q) ∧
      firstReadout S n u=0 ∧ secondReadout S n u q≠0 := by
  let x := BDL26RXFaceEdgeTower.faceOwner witnessScale witnessZ (Sum.inr witnessRectangle)
  let e := gradientError x (splitPotential x)
  have hzero : physicalReadout witnessScale 1 0=0 := physicalReadout_one_zero witnessScale
  have hne : physicalReadout witnessScale 1 e≠0 :=
    rectangle_physical_readout_nonzero witnessZ witnessRectangle
  obtain ⟨a,q,hq,ha,hb⟩ := physical_crossing witnessScale 1 e hzero hne
  refine ⟨witnessScale,1,physicalInput witnessScale 1 a,q,?_,ha,hb⟩
  exact gradientError_tower_support witnessZ (Sum.inr witnessRectangle) (splitPotential x) q hq
end QEC.Coding.BDL26RXFaceSecondReadout
