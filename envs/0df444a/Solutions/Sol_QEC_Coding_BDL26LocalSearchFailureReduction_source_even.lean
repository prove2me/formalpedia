-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSearchFailureReduction.source_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:05:32.988616+00:00
-- url     : https://prove2.me/submissions/c9ab22bf-af8a-42ff-aa59-4383543ca842

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_chiX_one_search_failure

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
theorem _root_.solution (S : OddScale) (k : Nat) (hk : 1 ≤ k)
    (u : XSyndromeDomain S (2*(k-1))) (q : Physical S (2*(k-1)+2))
    (hc : BDL26LogicalDefectProtection.chiX S (2*(k-1)) u q=1) :
    2*(k-1)+2=2*k ∧
      (firstReadout S (2*(k-1)) u≠0 ∨ localSearch S (secondReadout S (2*(k-1)) u q)=none) :=
  ⟨by omega,chiX_one_search_failure S _ u q hc⟩
end QEC.Coding.BDL26LocalSearchFailureReduction
