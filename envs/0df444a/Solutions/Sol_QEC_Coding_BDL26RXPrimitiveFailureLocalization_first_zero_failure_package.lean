-- Prove2me | solution 1 for QEC.Coding.BDL26RXPrimitiveFailureLocalization.first_zero_failure_package
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:07:26.345157+00:00
-- url     : https://prove2.me/submissions/cddf0f31-5af2-4f1b-bd6d-b2bcb6b7c988

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Theorems.Thm_QEC_Coding_BDL26RXPrimitiveFailureLocalization_first_zero_primitive
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_first_zero_no_local_preimage
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_first_zero_search_none
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_first_zero_second_nonzero


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
    (hc : BDL26LogicalDefectProtection.chiX S N u q=1) :
    (∃ (b : Nat) (hb : b≤N) (p : Primitive S b), parse S N q=.primitive p ∧
      (BDL26BoundaryTailInvariance.snapshot S N u q ⟨b,Nat.lt_succ_of_le hb⟩).word=
        canonicalBasisWord (F:=F) p.physical) ∧
    BDL26LevelTwoLocalBranchEndpoint.localSearch S (secondReadout S N u q)=none ∧
    (¬∃ e : BDL26LevelTwoLocalBranchEndpoint.Error S, levelTwoLocalError S e ∧
      BDL26LevelTwoLocalBranchEndpoint.delta S e=secondReadout S N u q) ∧
    secondReadout S N u q≠0 :=
  ⟨first_zero_primitive S N u q hs hc,
    BDL26LocalSearchFailureReduction.first_zero_search_none S N u q hs hc,
    BDL26LocalSearchFailureReduction.first_zero_no_local_preimage S N u q hs hc,
    BDL26LocalSearchFailureReduction.first_zero_second_nonzero S N u q hs hc⟩
end QEC.Coding.BDL26RXPrimitiveFailureLocalization
