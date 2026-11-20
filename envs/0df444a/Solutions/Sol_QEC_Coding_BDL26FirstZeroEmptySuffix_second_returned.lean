-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroEmptySuffix.second_returned
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:11:41.865656+00:00
-- url     : https://prove2.me/submissions/166ae351-4ec6-4a68-b267-8b88eeaf5485

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_second_search
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_second_search


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstZeroEmptySuffix
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstZeroEmptySuffix
theorem _root_.solution (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (hs : firstReadout S 0 u=0) :
    ∃ w : Word F (BDL26LevelTwoDecoder.ExecutableQ S),
      BDL26LevelTwoLocalBranchEndpoint.localSearch S (secondReadout S 0 u q)=some w ∧
      D S (secondReadout S 0 u q)=BDL26LevelTwoDecoder.toActualError S w ∧
      levelTwoLocalError S (D S (secondReadout S 0 u q)) ∧
      delta S (D S (secondReadout S 0 u q))=secondReadout S 0 u q := by
  obtain ⟨w,hw⟩ := second_search S u q hs
  exact ⟨w,hw,BDL26LevelTwoLocalBranchEndpoint.returned_word S _ w hw,
    BDL26LevelTwoLocalBranchEndpoint.returned_local_and_syndrome S _ w hw⟩
end QEC.Coding.BDL26FirstZeroEmptySuffix
