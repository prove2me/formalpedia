-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.lowerSyndromeRaw_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:40:54.681784+00:00
-- url     : https://prove2.me/submissions/8c1d7745-3ee5-445a-83d7-e63397a5aae8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_extendedRadialGauge_supported
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_coboundary1_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks
open BDL26OwnerParentObstruction BDL26ReplacementSupport BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26UniformHistoryObstruction
theorem _root_.solution (S : OddScale) (n : Nat) (z : RX2 (state S n).presentation S)
    (hz : (lowerSyndromeRaw S n) z ≠ 0) :
    rxSyndromeOwner (state S n).presentation S z = .x (retainedX S n) := by
  by_contra h
  apply hz
  unfold lowerSyndromeRaw lowerErrorRaw
  rw [rxPresentation_coboundary1_eq _ (state S n).admissible (state S n).regular]
  exact extendedRadialGauge_supported _ _ _ _ _ _ z h
end QEC.Coding.BDL26UniformHistoryObstruction
