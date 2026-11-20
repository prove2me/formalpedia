-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSearchFailureReduction.first_zero_no_local_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:16:57.325204+00:00
-- url     : https://prove2.me/submissions/ec1d7074-6647-4969-b3d9-37693342726c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_first_zero_search_none
import Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_localSearch_none_iff


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
    (hc : BDL26LogicalDefectProtection.chiX S n u q=1) :
    ¬∃ e : Error S, levelTwoLocalError S e ∧ delta S e=secondReadout S n u q :=
  (BDL26LevelTwoLocalBranchEndpoint.localSearch_none_iff S _).mp
    (first_zero_search_none S n u q hs hc)
end QEC.Coding.BDL26LocalSearchFailureReduction
