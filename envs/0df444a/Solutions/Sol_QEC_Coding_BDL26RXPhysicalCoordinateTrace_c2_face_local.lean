-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalCoordinateTrace.c2_face_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:28:50.777252+00:00
-- url     : https://prove2.me/submissions/751710a4-5843-4853-9af6-ecce5efaa83a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_levelTwoState_eq_pair

section
noncomputable section
namespace QEC.Coding.BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26OwnerIncidenceMasks
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder
open scoped Classical BigOperators
private theorem star_operations_heq {P Q : TannerSquarePresentation} (hp : P=Q) :
    HEq (BDL26RXPhysicalStarTransport.physicalXStar P)
      (BDL26RXPhysicalStarTransport.physicalXStar Q) ∧
    HEq (fun w : Word F P.Q => hammingSupport w) (fun w : Word F Q.Q => hammingSupport w) := by
  cases hp
  exact ⟨HEq.rfl,HEq.rfl⟩
end QEC.Coding.BDL26RXPhysicalCoordinateTrace
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26OwnerIncidenceMasks
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXPhysicalCoordinateTrace
theorem _root_.solution (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : BDL26RXFaceEdgeTower.Seed S)
    (hh : hammingSupport (descent S N u q).word ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation
        (BDL26RXFaceEdgeTower.faceOwner S a.1 a.2.1)) :
    levelTwoLocalError S (descent S N u q).word := by
  have hops := star_operations_heq
    (congrArg ConstructionState.presentation (levelTwoState_eq_pair S))
  have hstar : (BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation :
      (RawTwo S).X → Finset (RawTwo S).Q)=
      BDL26RXPhysicalStarTransport.physicalXStar (RawTwo S) := eq_of_heq hops.1
  have hsupport : ((fun w : Word F (state S 2).presentation.Q => hammingSupport w) :
      BDL26LevelTwoLocalBranchEndpoint.Error S → Finset (RawTwo S).Q)=
      (fun w : BDL26LevelTwoLocalBranchEndpoint.Error S => hammingSupport w) := eq_of_heq hops.2
  apply BDL26FirstZeroFaceEndpoint.face_local S a.1 a.2.1 (descent S N u q).word
  intro r hr
  have hs := congrArg (fun f : BDL26LevelTwoLocalBranchEndpoint.Error S → Finset (RawTwo S).Q =>
    f (descent S N u q).word) hsupport
  have hx := congrArg (fun f : (RawTwo S).X → Finset (RawTwo S).Q =>
    f (BDL26RXFaceEdgeTower.faceOwner S a.1 a.2.1)) hstar
  exact Eq.mp (congrArg (fun a : Finset (RawTwo S).Q => r∈a) hx)
    (hh (Eq.mpr (congrArg (fun a : Finset (RawTwo S).Q => r∈a) hs) hr))
end QEC.Coding.BDL26RXPhysicalCoordinateTrace
