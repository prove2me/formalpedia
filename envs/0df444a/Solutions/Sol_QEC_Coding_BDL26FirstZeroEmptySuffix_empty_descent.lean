-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroEmptySuffix.empty_descent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:42:48.094462+00:00
-- url     : https://prove2.me/submissions/d5fef94e-b591-4e0c-af29-658ef8a0ae62

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_empty_suffix
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_empty_suffix


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
theorem _root_.solution (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2) :
    (descent S 0 u q).word=flip S 0 q ∧ accumulated S 0 u q=0 :=
  BDL26ActualFailureReadout.empty_suffix S u q
end QEC.Coding.BDL26FirstZeroEmptySuffix
