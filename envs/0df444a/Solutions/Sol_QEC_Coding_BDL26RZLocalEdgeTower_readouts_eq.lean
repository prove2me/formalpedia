-- Prove2me | solution 1 for QEC.Coding.BDL26RZLocalEdgeTower.readouts_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:24:46.477497+00:00
-- url     : https://prove2.me/submissions/0d01fbf2-45e4-4ff9-9c4b-e8b0cc11fd74

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_tail_readouts_eq


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
    actualReadout S n (input S n u) b=
      actualReadout S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) b :=
  BDL26BoundaryTailInvariance.tail_readouts_eq S n _ _
    (BDL26BoundaryTailInvariance.physicalTop S n u q) (seedIndex t) 0
    (seed_boundary S n u q t) b hb
end QEC.Coding.BDL26RZLocalEdgeTower
