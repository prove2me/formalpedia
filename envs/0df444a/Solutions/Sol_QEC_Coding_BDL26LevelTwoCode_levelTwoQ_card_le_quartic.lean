-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoCode.levelTwoQ_card_le_quartic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:58:30.697395+00:00
-- url     : https://prove2.me/submissions/1917c8f9-7a2c-4a6d-9e84-ca44e6121250

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_levelTwoQ_card_upper

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators
namespace QEC.Coding.BDL26LevelTwoCode
theorem _root_.solution (S : OddScale) :
    Fintype.card (levelTwoPresentation S).Q ≤ 288 * S.ell ^ 4 := by
  have hthree := S.three_le
  have hsum : S.ell + 2 ≤ 3 * S.ell := by omega
  have hfactor : 2 * S.ell * (S.ell + 2) ≤ 6 * S.ell ^ 2 := by
    calc
      _ ≤ 2 * S.ell * (3 * S.ell) := Nat.mul_le_mul_left _ hsum
      _ = 6 * S.ell ^ 2 := by ring
  calc
    _ ≤ 8 * (2 * S.ell * (S.ell + 2)) ^ 2 := levelTwoQ_card_upper S
    _ ≤ 8 * (6 * S.ell ^ 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hfactor 2)
    _ = 288 * S.ell ^ 4 := by ring
end QEC.Coding.BDL26LevelTwoCode
