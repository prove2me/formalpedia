-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.lowerError_eq_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:39:36.217004+00:00
-- url     : https://prove2.me/submissions/e01b94bf-a035-4bd1-b6f0-b7a281bd80bb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_lowerErrorRaw_eq_basis
section
namespace QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26XLocalRadialParity BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators
private theorem basis_transport (P U : TannerSquarePresentation) (h : P = U) (q : U.Q) :
    Eq.mpr (congrArg (fun T : TannerSquarePresentation => Word BDL26Field T.Q) h)
      (canonicalBasisWord q) =
    canonicalBasisWord (Eq.mpr (congrArg TannerSquarePresentation.Q h) q) := by
  cases h
  rfl
end QEC.Coding.BDL26UniformHistoryObstruction
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26XLocalRadialParity BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26UniformHistoryObstruction
theorem _root_.solution (S : OddScale) (j : Nat) :
    lowerError S j = canonicalBasisWord (lowerBasis S j) := by
  unfold lowerError
  rw [lowerErrorRaw_eq_basis]
  exact basis_transport _ _
    (congrArg ConstructionState.presentation (state_rx S (2 * j + 2) (by omega))) _
end QEC.Coding.BDL26UniformHistoryObstruction
