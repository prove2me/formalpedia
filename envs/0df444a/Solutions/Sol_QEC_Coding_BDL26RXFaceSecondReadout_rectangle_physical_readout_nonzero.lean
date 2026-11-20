-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceSecondReadout.rectangle_physical_readout_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:13:59.152725+00:00
-- url     : https://prove2.me/submissions/ca1d334c-cfc3-41b3-b3b6-ce424d457995

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
import Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_physicalReadout_one
import Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_split_coarse_eq_root_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_rectangle_root_nonclosed

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
theorem _root_.solution (z : One.Z)
    (rect : SubdivisionBoundaryEdge (transposePresentation One) z witnessScale) :
    physicalReadout witnessScale 1
      (gradientError (BDL26RXFaceEdgeTower.faceOwner witnessScale z (Sum.inr rect))
        (splitPotential (BDL26RXFaceEdgeTower.faceOwner witnessScale z (Sum.inr rect))))≠0 := by
  rw [physicalReadout_one]
  change (BDL26RXDecoderAdapter.rxStepOutput witnessScale 3 rxIndex rxIndex_even
    (gradientInput (BDL26RXFaceEdgeTower.faceOwner witnessScale z (Sum.inr rect))
      (splitPotential (BDL26RXFaceEdgeTower.faceOwner witnessScale z (Sum.inr rect))))).coarse.val≠0
  rw [split_coarse_eq_root_syndrome]
  exact rectangle_root_nonclosed z rect
end QEC.Coding.BDL26RXFaceSecondReadout
