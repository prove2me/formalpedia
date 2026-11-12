-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoCode.levelTwoFace_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:58:13.904253+00:00
-- url     : https://prove2.me/submissions/3455afaf-ae69-4f70-b05f-71cadf54dd61

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_rzPresentationFace_card

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators
namespace QEC.Coding.BDL26LevelTwoCode
theorem _root_.solution (S : OddScale) :
    Fintype.card (levelTwoPresentation S).Face =
      (∑ z : (levelOnePresentation S).Z,
        Fintype.card (ZDoubleCylinderFace (levelOnePresentation S) z S) * (2 * 2)) +
      ((∑ e : QZEdge (levelOnePresentation S),
        Fintype.card (QDoubleCylinderEdge
          (transposePresentation (levelOnePresentation S)) e.1.1 S) * 2) +
       Fintype.card (levelOnePresentation S).Face * 2) := by
  exact rzPresentationFace_card (levelOnePresentation S)
    (rxState S baseState).admissible.toTannerSquareAdmissible S
end QEC.Coding.BDL26LevelTwoCode
