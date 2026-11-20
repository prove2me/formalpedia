-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSearchFailureReduction.search_none_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:21:43.54319+00:00
-- url     : https://prove2.me/submissions/1e0c36cd-598c-45b0-b66e-9803c0bf053e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
import Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_zero_branch
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
theorem _root_.solution (S : OddScale) (t : Syndrome S)
    (hn : localSearch S t=none) : t≠0 := by
  intro ht
  rw [ht] at hn
  obtain ⟨w,hw⟩ := BDL26LevelTwoLocalBranchEndpoint.zero_branch S
  have hw' : localSearch S (0 : Syndrome S)=some w := hw
  have hnone : (none : Option (Word F (BDL26LevelTwoDecoder.ExecutableQ S)))=some w :=
    hn.symm.trans hw'
  cases hnone
end QEC.Coding.BDL26LocalSearchFailureReduction
