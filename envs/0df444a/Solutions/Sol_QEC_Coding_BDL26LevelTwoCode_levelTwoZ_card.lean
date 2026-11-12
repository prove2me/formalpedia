-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoCode.levelTwoZ_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:57:57.892203+00:00
-- url     : https://prove2.me/submissions/82d65898-10a9-4dff-a9ae-9a9fabff7cfe

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_rzPresentationZ_card

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators
namespace QEC.Coding.BDL26LevelTwoCode
theorem _root_.solution (S : OddScale) :
    Fintype.card (levelTwoPresentation S).Z =
      ∑ z : (levelOnePresentation S).Z,
        Fintype.card (ZDoubleCylinderVertex (levelOnePresentation S) z S) := by
  exact rzPresentationZ_card (levelOnePresentation S)
    (rxState S baseState).admissible.toTannerSquareAdmissible S
end QEC.Coding.BDL26LevelTwoCode
