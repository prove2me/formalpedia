-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.dualHistory_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:45:39.543714+00:00
-- url     : https://prove2.me/submissions/99f9f5ad-6e3b-4001-a1fc-2bc787ce48c1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_stoppedHistory_length


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZMap1CoordinateBridge MultiscaleDecoder
open PauliSymplectic BDL26CSSHamiltonian
open scoped Classical BigOperators
namespace QEC.Coding.BDL26TransposedStoppedDecoder
theorem _root_.solution (S : OddScale) (n : Nat)
    (sigma : (dualFamily S (n + 2)).Syndrome (TopIndex (n + 2))) :
    (dualHistory S n sigma).length = n + 1 :=
  LevelTwoHistory.stoppedHistory_length _ (dualAboveTwoSteps S n) (dualBase S n) sigma
end QEC.Coding.BDL26TransposedStoppedDecoder
