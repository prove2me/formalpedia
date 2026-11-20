-- Prove2me | solution 1 for QEC.Coding.BDL26RXPrimitiveFailureLocalization.zero_correction_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:00:49.568835+00:00
-- url     : https://prove2.me/submissions/9dd74d4d-089f-4d68-a4af-02651f98b2e5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Theorems.Thm_QEC_Coding_BDL26RXPrimitiveFailureLocalization_zero_full_spec

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPrimitiveFailureLocalization
open MultiscaleDecoder PauliSymplectic BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26OwnerIncidenceMasks
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder BDL26RXPhysicalCoordinateTrace
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXPrimitiveFailureLocalization
theorem _root_.solution (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : LevelIndex N)
    (hz : (BDL26BoundaryTailInvariance.snapshot S N u q a).word=0) :
    (SuffixData S N).family.coboundary0 (TopIndex N) (zeroFullPotential S N u q a hz)=
      flip S N q+xCorrection S N u+xCorrection S N (translateX S N u (flip S N q)) := by
  rw [zero_full_spec S N u q a hz]
  unfold BDL26LogicalDefectProtection.deltaX BDL26ActualFailureReadout.flip
  ac_rfl
end QEC.Coding.BDL26RXPrimitiveFailureLocalization
