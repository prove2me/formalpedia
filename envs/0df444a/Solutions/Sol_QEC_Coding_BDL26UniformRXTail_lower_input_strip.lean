-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.lower_input_strip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:19:11.227295+00:00
-- url     : https://prove2.me/submissions/fd10e060-6135-441b-bfdb-10d607c1050a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_extendXCorrection_delta_at_x
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_coboundary1_eq
import Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_radialGauge_strip_coboundary
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26DecodingGraph BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26IndexedDecoder
open BDL26UniformHistoryObstruction BDL26OwnerParentObstruction
open BDL26RXLocalReplacement BDL26XLocalRadialParity
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26UniformRXTail
theorem _root_.solution (S : OddScale) (n : Nat)
    (face : XStarFace (state S n).presentation (retainedX S n))
    (side : Fin 2) (i : Fin S.half) :
    lowerSyndromeRaw S n (.inl (.inl ⟨retainedX S n,
      .inr (subdivisionOriginalBoundaryEdge (state S n).presentation (retainedX S n) S
        (xStarFaceBoundaryEdge (state S n).presentation (retainedX S n) face side) i)⟩)) = 0 := by
  unfold lowerSyndromeRaw lowerErrorRaw
  rw [rxPresentation_coboundary1_eq _ (state S n).admissible (state S n).regular]
  refine (extendXCorrection_delta_at_x (state S n).presentation S (retainedX S n)
    (radialGauge (state S n).presentation (state S n).admissible.toTannerSquareAdmissible
      (retainedX S n) S 0 (retainedAlpha S n))
      (.inr (subdivisionOriginalBoundaryEdge (state S n).presentation (retainedX S n) S
        (xStarFaceBoundaryEdge (state S n).presentation (retainedX S n) face side) i))).trans ?_
  exact radialGauge_strip_coboundary _ _ _ _ _ _ _ _ _
end QEC.Coding.BDL26UniformRXTail
