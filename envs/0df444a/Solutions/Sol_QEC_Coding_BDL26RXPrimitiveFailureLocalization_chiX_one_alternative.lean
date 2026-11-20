-- Prove2me | solution 1 for QEC.Coding.BDL26RXPrimitiveFailureLocalization.chiX_one_alternative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:07:16.123209+00:00
-- url     : https://prove2.me/submissions/1f9653b8-567f-49c9-89f2-d8d016843308

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Theorems.Thm_QEC_Coding_BDL26RXPrimitiveFailureLocalization_first_zero_primitive

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
    (q : Physical S (N+2)) (hc : BDL26LogicalDefectProtection.chiX S N u q=1) :
    firstReadout S N u≠0 ∨ ∃ (b : Nat) (hb : b≤N) (p : Primitive S b),
      parse S N q=.primitive p ∧
      (BDL26BoundaryTailInvariance.snapshot S N u q ⟨b,Nat.lt_succ_of_le hb⟩).word=
        canonicalBasisWord (F:=F) p.physical := by
  by_cases hs : firstReadout S N u=0
  · exact Or.inr (first_zero_primitive S N u q hs hc)
  · exact Or.inl hs
end QEC.Coding.BDL26RXPrimitiveFailureLocalization
