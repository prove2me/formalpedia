-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroFaceEndpoint.empty_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:25:43.62018+00:00
-- url     : https://prove2.me/submissions/fe115af3-264f-4e97-a798-dcf1389fbf44

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_first_zero_chiX
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_empty_suffix


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstZeroFaceEndpoint
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstZeroFaceEndpoint
theorem _root_.solution (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hs : firstReadout S 0 u=0) (hf : terminalFace S 0 u q z f) :
    (descent S 0 u q).word=flip S 0 q ∧ accumulated S 0 u q=0 ∧
      BDL26LogicalDefectProtection.chiX S 0 u q=0 :=
  ⟨(BDL26ActualFailureReadout.empty_suffix S u q).1,
    (BDL26ActualFailureReadout.empty_suffix S u q).2,first_zero_chiX S 0 u q z f hs hf⟩
end QEC.Coding.BDL26FirstZeroFaceEndpoint
