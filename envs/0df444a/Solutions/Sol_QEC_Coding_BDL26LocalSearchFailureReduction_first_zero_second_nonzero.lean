-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSearchFailureReduction.first_zero_second_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:19:12.386103+00:00
-- url     : https://prove2.me/submissions/7ce4d77a-608b-4d0e-a988-6c90d7d94ff1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_first_zero_search_none
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_search_none_nonzero

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
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (hc : BDL26LogicalDefectProtection.chiX S n u q=1) : secondReadout S n u q≠0 :=
  search_none_nonzero S _ (first_zero_search_none S n u q hs hc)
end QEC.Coding.BDL26LocalSearchFailureReduction
