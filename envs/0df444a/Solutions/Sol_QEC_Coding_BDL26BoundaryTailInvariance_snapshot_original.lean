-- Prove2me | solution 1 for QEC.Coding.BDL26BoundaryTailInvariance.snapshot_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:55:16.274881+00:00
-- url     : https://prove2.me/submissions/7aacb6b5-e83e-4f7a-80d3-6e2474607e13

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
    (q : Physical S (n+2)) (a : LevelIndex n) : snapshot S n u q a=
      actualDescent S n (input S n u) (BDL26ActualFailureReadout.flip S n q) (elementaryCenter S n q)
        (physical_supported S n q) a := rfl
end QEC.Coding.BDL26BoundaryTailInvariance
