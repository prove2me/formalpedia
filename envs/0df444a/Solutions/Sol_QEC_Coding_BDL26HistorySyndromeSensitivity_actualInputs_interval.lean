-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.actualInputs_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:05:56.41953+00:00
-- url     : https://prove2.me/submissions/c7f00305-b867-479a-bc74-1605e0631d28

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_prefixInput_comp


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (sigma : TopInput S n) (b a : LevelIndex n)
    (ha : a.val ≤ b.val) :
    actualInputs S n sigma a =
      prefixInput (SuffixData S n) (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n))
        b.val (Nat.le_of_lt_succ b.isLt) (actualInputs S n sigma b) a ha :=
  prefixInput_comp (SuffixData S n)
    (LevelTwoHistory.suffixSteps (indexedDecoderData S (n+2)) (actualAboveTwoSteps S n))
    n (Nat.le_refl _) sigma b a (Nat.le_of_lt_succ b.isLt) ha
end QEC.Coding.BDL26HistorySyndromeSensitivity
