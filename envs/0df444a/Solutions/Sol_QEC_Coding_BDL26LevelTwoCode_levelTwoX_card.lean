-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoCode.levelTwoX_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:57:34.723321+00:00
-- url     : https://prove2.me/submissions/8870fde6-3ba0-4c41-ba6e-41d500e8dc1b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_rzPresentationX_card

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators
namespace QEC.Coding.BDL26LevelTwoCode
theorem _root_.solution (S : OddScale) :
    Fintype.card (levelTwoPresentation S).X =
      ((∑ z : (levelOnePresentation S).Z,
        Fintype.card (ZDoubleCylinderFace (levelOnePresentation S) z S)) +
       (∑ q : (levelOnePresentation S).Q,
        Fintype.card (QDoubleCylinderEdge (transposePresentation (levelOnePresentation S)) q S))) +
      Fintype.card (levelOnePresentation S).X * 2 := by
  exact rzPresentationX_card (levelOnePresentation S)
    (rxState S baseState).admissible.toTannerSquareAdmissible S
end QEC.Coding.BDL26LevelTwoCode
