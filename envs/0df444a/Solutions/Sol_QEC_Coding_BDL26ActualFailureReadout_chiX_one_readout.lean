-- Prove2me | solution 1 for QEC.Coding.BDL26ActualFailureReadout.chiX_one_readout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:13:23.468638+00:00
-- url     : https://prove2.me/submissions/be40fcb2-279f-4835-ab34-fa56be25f3c3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoOldXStarEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_chiX_zero
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ActualFailureReadout
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian
open scoped Classical BigOperators
namespace QEC.Coding.BDL26ActualFailureReadout
theorem _root_.solution (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hc : BDL26LogicalDefectProtection.chiX S n u q=1) :
    firstReadout S n u≠0 ∨ secondReadout S n u q≠0 := by
  by_cases hs : firstReadout S n u=0
  · by_cases ht : secondReadout S n u q=0
    · exact False.elim (one_ne_zero (hc.symm.trans (chiX_zero S n u q hs ht)))
    · exact Or.inr ht
  · exact Or.inl hs
end QEC.Coding.BDL26ActualFailureReadout
