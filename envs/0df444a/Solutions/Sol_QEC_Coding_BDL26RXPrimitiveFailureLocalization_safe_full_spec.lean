-- Prove2me | solution 1 for QEC.Coding.BDL26RXPrimitiveFailureLocalization.safe_full_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:40:20.914585+00:00
-- url     : https://prove2.me/submissions/d3b4c106-ad91-44c5-bdb7-f80108f5d5ad

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_fullPotential_spec


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
    (q : Physical S (N+2)) (hs : firstReadout S N u=0)
    (hSafe : (parse S N q).safe=true) :
    (SuffixData S N).family.coboundary0 (TopIndex N) (safeFullPotential S N u q hs hSafe)=
      BDL26LogicalDefectProtection.deltaX S N u q :=
  BDL26LocalSearchFailureReduction.fullPotential_spec S N u q hs (safe_search S N u q hs hSafe)
end QEC.Coding.BDL26RXPrimitiveFailureLocalization
