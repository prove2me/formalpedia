-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroEmptySuffix.second_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:01:43.965174+00:00
-- url     : https://prove2.me/submissions/1181a4bc-ed5f-4f00-a63d-3b7e3650c813

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_physical_flip_search
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_second_syndrome

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
    BDL26LevelTwoLocalBranchEndpoint.localSuccess S (secondReadout S 0 u q) := by
  rw [← second_syndrome S u q hs]
  exact physical_flip_search S q
end QEC.Coding.BDL26FirstZeroEmptySuffix
