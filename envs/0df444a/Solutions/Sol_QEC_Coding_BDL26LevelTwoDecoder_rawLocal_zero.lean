-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDecoder.rawLocal_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:47:42.806086+00:00
-- url     : https://prove2.me/submissions/1b4e45de-4c78-44b9-9807-88a6cf0f70e5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDecoder
open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26TannerLocalRegularity BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
namespace QEC.Coding.BDL26LevelTwoDecoder
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (center : Vertex P) : rawLocal P S 0 = true := by
  apply decide_eq_true
  exact ⟨center, by intro q h; exact (h rfl).elim⟩
end QEC.Coding.BDL26LevelTwoDecoder
