-- Prove2me | solution 1 for QEC.Coding.BDL26BoundaryTailInvariance.actual_Y_dressed_Z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:55:41.803368+00:00
-- url     : https://prove2.me/submissions/31559a32-69da-4f45-bbe2-e16f919643ff

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_physical_Y_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_physical_Y_dressed_Z


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
open QEC.Semantics BDL26PairedDecoderPhase
namespace QEC.Coding.BDL26BoundaryTailInvariance
theorem _root_.solution (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n s.1 q a).word) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q .y*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .y)*atom S n s=0 :=
  physical_Y_dressed_Z S n s q a p hp
end QEC.Coding.BDL26BoundaryTailInvariance
