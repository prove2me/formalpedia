-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.dualHistory_base_readout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:47:18.818215+00:00
-- url     : https://prove2.me/submissions/7ee0d5b8-d4df-402d-a889-231f89ca9d9c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_stoppedHistory_base_readout


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
    LevelTwoHistory.syndromeReadout (dualDecoderData S (n + 2)) (dualHistory S n sigma)
      (LevelTwoHistory.physicalLevel (0 : LevelIndex n)) =
      (terminalInput (LevelTwoHistory.suffixData (dualDecoderData S (n + 2)))
        (LevelTwoHistory.suffixSteps _ (dualAboveTwoSteps S n)) sigma).val :=
  LevelTwoHistory.stoppedHistory_base_readout _ (dualAboveTwoSteps S n) (dualBase S n) sigma
end QEC.Coding.BDL26TransposedStoppedDecoder
