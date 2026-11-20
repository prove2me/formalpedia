-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroEmptySuffix.physical_flip_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:08:57.218162+00:00
-- url     : https://prove2.me/submissions/bd35a982-91f8-4546-9ff3-072fd14a24a3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_physical_flip_local
import Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_localSuccess_iff


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
theorem _root_.solution (S : OddScale) (q : Physical S 2) :
    BDL26LevelTwoLocalBranchEndpoint.localSuccess S (delta S (flip S 0 q)) :=
  (BDL26LevelTwoLocalBranchEndpoint.localSuccess_iff S _).mpr
    ⟨flip S 0 q,physical_flip_local S q,rfl⟩
end QEC.Coding.BDL26FirstZeroEmptySuffix
