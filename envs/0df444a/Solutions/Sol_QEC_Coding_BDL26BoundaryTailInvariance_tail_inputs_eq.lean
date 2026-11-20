-- Prove2me | solution 1 for QEC.Coding.BDL26BoundaryTailInvariance.tail_inputs_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:51:27.317116+00:00
-- url     : https://prove2.me/submissions/cac2840b-9829-4a7e-bbbe-7a41a45a0c23

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_tail_potential_spec

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
theorem _root_.solution (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(path S n sigma tau top a).word)
    (b : LevelIndex n) (hb : b.val≤a.val) : actualInputs S n sigma b=actualInputs S n tau b :=
  inputs_eq S n sigma tau b _ _ (tail_potential_spec S n sigma tau top a p hp b hb)
end QEC.Coding.BDL26BoundaryTailInvariance
