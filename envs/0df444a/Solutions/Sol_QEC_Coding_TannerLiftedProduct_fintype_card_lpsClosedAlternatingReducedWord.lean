-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.fintype_card_lpsClosedAlternatingReducedWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:37:40.374836+00:00
-- url     : https://prove2.me/submissions/f91c3391-40a6-4c6e-ac78-4e26336e8bb3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ) :
    Fintype.card (LPSClosedAlternatingReducedWord a n) =
      lpsAlternatingClosedReducedWordCount a n := by
  classical
  induction n using Nat.twoStepInduction with
  | zero =>
      change Fintype.card
          {word : LPSReducedWord a.degreePrime.pos 0 //
            lpsPSLWordProduct a word.1.1 = 1} =
        (lpsClosedReducedWords a 0).card
      rw [Fintype.card_congr (lpsClosedReducedWordSubtypeEquiv a 0),
        Fintype.card_coe]
  | one =>
      change Fintype.card
          {word : LPSReducedWord a.degreePrime.pos 1 //
            lpsPSLWordProduct a word.1.1 = 1} =
        (lpsClosedReducedWords a 1).card
      rw [Fintype.card_congr (lpsClosedReducedWordSubtypeEquiv a 1),
        Fintype.card_coe]
  | more n hn _hnOne =>
      rw [lpsAlternatingClosedReducedWordCount]
      calc
        Fintype.card (LPSClosedAlternatingReducedWord a (n + 2)) =
            Fintype.card
              ({word : LPSReducedWord a.degreePrime.pos (n + 2) //
                  lpsPSLWordProduct a word.1.1 = 1} ⊕
                LPSClosedAlternatingReducedWord a n) := by
                  exact Fintype.card_congr
                    (lpsClosedAlternatingReducedWordAddTwoEquiv a n)
        _ = Fintype.card
              {word : LPSReducedWord a.degreePrime.pos (n + 2) //
                lpsPSLWordProduct a word.1.1 = 1} +
              Fintype.card (LPSClosedAlternatingReducedWord a n) :=
                Fintype.card_sum
        _ = (lpsClosedReducedWords a (n + 2)).card +
              lpsAlternatingClosedReducedWordCount a n := by
                rw [Fintype.card_congr
                  (lpsClosedReducedWordSubtypeEquiv a (n + 2)),
                  Fintype.card_coe, hn]
end QEC.Coding.TannerLiftedProduct
