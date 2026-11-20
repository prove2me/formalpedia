-- Prove2me | solution 1 for QEC.Coding.BDL26RZLocalEdgeTower.chiX_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:26:32.200498+00:00
-- url     : https://prove2.me/submissions/a5c36376-8414-410c-80f3-a3a9830add5d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_physical_chiX_zero


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
    (q : Physical S (n+2)) (t : Killed S n q) :
    BDL26LogicalDefectProtection.chiX S n u q=0 :=
  BDL26BoundaryTailInvariance.physical_chiX_zero S n u q (seedIndex t) 0
    (seed_boundary S n u q t)
end QEC.Coding.BDL26RZLocalEdgeTower
