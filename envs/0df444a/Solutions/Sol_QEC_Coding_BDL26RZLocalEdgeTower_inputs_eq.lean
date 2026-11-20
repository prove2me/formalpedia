-- Prove2me | solution 1 for QEC.Coding.BDL26RZLocalEdgeTower.inputs_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:25:36.363354+00:00
-- url     : https://prove2.me/submissions/97c376d7-2d96-47eb-89cb-2a86b659df50

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_physical_readouts_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZLocalEdgeTower
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26TransposedStoppedDecoder
open PauliSymplectic
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RZLocalEdgeTower
theorem _root_.solution (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) (b : LevelIndex n)
    (hb : b.val ≤ seedDepth t) :
    actualInputs S n (input S n u) b=
      actualInputs S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) b :=
  BDL26BoundaryTailInvariance.physical_readouts_eq S n u q (seedIndex t) 0
    (seed_boundary S n u q t) b hb
end QEC.Coding.BDL26RZLocalEdgeTower
