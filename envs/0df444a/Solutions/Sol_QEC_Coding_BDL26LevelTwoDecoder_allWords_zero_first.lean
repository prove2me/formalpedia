-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDecoder.allWords_zero_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:49:25.218696+00:00
-- url     : https://prove2.me/submissions/d339cc23-7d4b-41a8-895e-259802c0ee39

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_wordsOn_zero_first

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDecoder
open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26TannerLocalRegularity BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
namespace QEC.Coding.BDL26LevelTwoDecoder
theorem _root_.solution (α : Type) [Fintype α] [Encodable α] [DecidableEq α] :
    ∃ tail, allWords α = (0 : Word (ZMod 2) α) :: tail :=
  wordsOn_zero_first (coordinates α)
end QEC.Coding.BDL26LevelTwoDecoder
