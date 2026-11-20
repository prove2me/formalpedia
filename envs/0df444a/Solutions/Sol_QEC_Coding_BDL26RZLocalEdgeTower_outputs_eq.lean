-- Prove2me | solution 1 for QEC.Coding.BDL26RZLocalEdgeTower.outputs_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:24:49.879195+00:00
-- url     : https://prove2.me/submissions/cc37bca1-7d05-4a6c-a9ce-56679bbf7fce

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_tail_outputs_eq


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
    (q : Physical S (n+2)) (t : Killed S n q) (i : StepIndex n)
    (hi : i.succ.val ≤ seedDepth t) :
    actualOutput S n (input S n u) i=
      actualOutput S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) i :=
  BDL26BoundaryTailInvariance.tail_outputs_eq S n _ _
    (BDL26BoundaryTailInvariance.physicalTop S n u q) (seedIndex t) 0
    (seed_boundary S n u q t) i hi
end QEC.Coding.BDL26RZLocalEdgeTower
