-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalCoordinateTrace.parser_semantics
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:02:19.679602+00:00
-- url     : https://prove2.me/submissions/4597aa7c-475f-495b-8e8f-03152e13bcaa

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalCoordinateTrace_trace_semantics
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_path_top
import Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_basis_supported


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26OwnerIncidenceMasks
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXPhysicalCoordinateTrace
theorem _root_.solution (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) :
    LeafMeaning S N (input S N u) (perturbTop S N (input S N u) (flip S N q))
      (BDL26BoundaryTailInvariance.physicalTop S N u q) (parse S N q) := by
  apply trace_semantics (parsedTrace S N q) N _ _ _ (Nat.le_refl _)
  rw [path_top]
  change hammingSupport (flip S N q) ⊆ {q}
  rw [flip_eq_basis]
  exact BDL26RXQEdgePairTransport.basis_supported q
end QEC.Coding.BDL26RXPhysicalCoordinateTrace
