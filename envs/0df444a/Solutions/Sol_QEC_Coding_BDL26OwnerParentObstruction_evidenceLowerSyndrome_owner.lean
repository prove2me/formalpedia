-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerParentObstruction.evidenceLowerSyndrome_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:15:57.691718+00:00
-- url     : https://prove2.me/submissions/4f6474fe-c456-4950-ae9c-755e70e9a15c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_extendedRadialGauge_supported
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_coboundary1_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerParentObstruction
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps MultiscaleDecoder
open scoped Classical
open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open scoped BigOperators
namespace QEC.Coding.BDL26OwnerParentObstruction
theorem _root_.solution (z : RX2 evidenceStateTwo.presentation scaleFive)
    (hz : evidenceLowerSyndrome z ≠ 0) :
    rxSyndromeOwner evidenceStateTwo.presentation scaleFive z = .x evidenceX := by
  by_contra h
  apply hz
  unfold evidenceLowerSyndrome evidenceCorrection
  rw [rxPresentation_coboundary1_eq _ evidenceStateTwo.admissible evidenceStateTwo.regular]
  exact extendedRadialGauge_supported _ _ _ _ _ _ z h
end QEC.Coding.BDL26OwnerParentObstruction
