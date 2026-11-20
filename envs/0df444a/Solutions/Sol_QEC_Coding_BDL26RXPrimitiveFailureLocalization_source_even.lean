-- Prove2me | solution 1 for QEC.Coding.BDL26RXPrimitiveFailureLocalization.source_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:49:29.181631+00:00
-- url     : https://prove2.me/submissions/1809e2b1-924b-4f39-96c8-b46a6d74ce2e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Theorems.Thm_QEC_Coding_BDL26RXPrimitiveFailureLocalization_chiX_one_alternative

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
theorem _root_.solution (S : OddScale) (k : Nat) (hk : 1≤k)
    (u : XSyndromeDomain S (2*(k-1))) (q : Physical S (2*(k-1)+2))
    (hc : BDL26LogicalDefectProtection.chiX S (2*(k-1)) u q=1) :
    2*(k-1)+2=2*k ∧ (firstReadout S (2*(k-1)) u≠0 ∨
      ∃ (b : Nat) (hb : b≤2*(k-1)) (p : Primitive S b),
        parse S (2*(k-1)) q=.primitive p ∧
        (BDL26BoundaryTailInvariance.snapshot S (2*(k-1)) u q
          ⟨b,Nat.lt_succ_of_le hb⟩).word=canonicalBasisWord (F:=F) p.physical) :=
  ⟨by omega,chiX_one_alternative S _ u q hc⟩
end QEC.Coding.BDL26RXPrimitiveFailureLocalization
