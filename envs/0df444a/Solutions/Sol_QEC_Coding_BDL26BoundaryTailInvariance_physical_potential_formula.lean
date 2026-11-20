-- Prove2me | solution 1 for QEC.Coding.BDL26BoundaryTailInvariance.physical_potential_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:44:37.379877+00:00
-- url     : https://prove2.me/submissions/100cfa98-9f1a-4d05-9b37-6e4b11de48a4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundaryTailInvariance
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26TannerLocalRegularity
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26TransposedStoppedDecoder PauliSymplectic
open scoped Classical
namespace QEC.Coding.BDL26BoundaryTailInvariance
theorem _root_.solution (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n u q a).word) :
    physicalPotential S n u q a p hp=
      intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
        (tailPotential S n _ _ (physicalTop S n u q) a p hp 0 (Nat.zero_le _))+
        BDL26ActualFailureReadout.accumulated S n u q := rfl
end QEC.Coding.BDL26BoundaryTailInvariance
