-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSearchFailureReduction.chiX_one_search_failure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:55:06.705349+00:00
-- url     : https://prove2.me/submissions/d93cd8fd-53c8-45f3-8e90-7d764237672d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_some_chiX_zero
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalSearchFailureReduction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
namespace QEC.Coding.BDL26LocalSearchFailureReduction
theorem _root_.solution (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hc : BDL26LogicalDefectProtection.chiX S n u q=1) :
    firstReadout S n u≠0 ∨ localSearch S (secondReadout S n u q)=none := by
  by_cases hs : firstReadout S n u=0
  · right
    cases ht : localSearch S (secondReadout S n u q) with
    | none => rfl
    | some w =>
      exact False.elim (one_ne_zero (hc.symm.trans (some_chiX_zero S n u q hs w ht)))
  · exact Or.inl hs
end QEC.Coding.BDL26LocalSearchFailureReduction
