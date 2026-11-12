-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.dualHistory_zero_inputs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:46:06.689194+00:00
-- url     : https://prove2.me/submissions/46567437-c74a-487d-9036-fa897ec7d578

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualStepOutput_zero_coarse
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_stoppedHistory_zero_inputs


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZMap1CoordinateBridge MultiscaleDecoder
open PauliSymplectic BDL26CSSHamiltonian
open scoped Classical BigOperators
namespace QEC.Coding.BDL26TransposedStoppedDecoder
theorem _root_.solution (S : OddScale) (n : Nat)
    (sigma : (dualFamily S (n + 2)).Syndrome (TopIndex (n + 2))) (hs : sigma.val = 0) :
    ∀ e ∈ dualHistory S n sigma, e.inputSyndrome.2.val = 0 :=
  LevelTwoHistory.stoppedHistory_zero_inputs _ (dualAboveTwoSteps S n) (dualBase S n)
    (fun i _ sigma hz => dualStepOutput_zero_coarse S (n + 2) i sigma hz) sigma hs
end QEC.Coding.BDL26TransposedStoppedDecoder
