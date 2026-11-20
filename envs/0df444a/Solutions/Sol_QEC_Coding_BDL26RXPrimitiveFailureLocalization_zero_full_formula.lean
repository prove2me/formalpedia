-- Prove2me | solution 1 for QEC.Coding.BDL26RXPrimitiveFailureLocalization.zero_full_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:40:11.055972+00:00
-- url     : https://prove2.me/submissions/02c41f38-f611-4421-91b4-7ed86cb13d7f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_physical_potential_formula


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
    zeroFullPotential S N u q a hz=
      intervalMap0 (SuffixData S N) 0 (TopIndex N) (Nat.zero_le _)
        (BDL26BoundaryTailInvariance.tailPotential S N
          (input S N u) (perturbTop S N (input S N u) (flip S N q))
          (BDL26BoundaryTailInvariance.physicalTop S N u q) a 0
          (zero_boundary S N u q a hz) 0 (Nat.zero_le _))+accumulated S N u q :=
  BDL26BoundaryTailInvariance.physical_potential_formula S N u q a 0
    (zero_boundary S N u q a hz)
end QEC.Coding.BDL26RXPrimitiveFailureLocalization
