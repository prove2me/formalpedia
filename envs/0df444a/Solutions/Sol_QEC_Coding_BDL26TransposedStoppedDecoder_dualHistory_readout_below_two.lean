-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.dualHistory_readout_below_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:46:43.024323+00:00
-- url     : https://prove2.me/submissions/b8e80172-9f2e-4f1f-a786-52c2db77d240

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_syndromeReadout_below_two


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZMap1CoordinateBridge MultiscaleDecoder
open PauliSymplectic BDL26CSSHamiltonian
open scoped Classical BigOperators
namespace QEC.Coding.BDL26TransposedStoppedDecoder
theorem _root_.solution (S : OddScale) (n : Nat)
    (sigma : (dualFamily S (n + 2)).Syndrome (TopIndex (n + 2)))
    (i : LevelIndex (n + 2)) (hi : i.val < 2) :
    LevelTwoHistory.syndromeReadout (dualDecoderData S (n + 2)) (dualHistory S n sigma) i = 0 :=
  LevelTwoHistory.syndromeReadout_below_two _ _ i hi
end QEC.Coding.BDL26TransposedStoppedDecoder
