-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.actual_interval_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:25:23.855205+00:00
-- url     : https://prove2.me/submissions/dd39a606-19d5-4dc6-9c00-6733cb8eb19b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_rxCount_formula
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_propagate_card
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actual_interval_support
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (sigma tau : TopInput S n) (a b : LevelIndex n)
    (ha : a.val ≤ b.val) :
    HammingWeight (actualReadout S n sigma a + actualReadout S n tau a) ≤
      57 ^ ((b.val+1)/2 - (a.val+1)/2) *
        HammingWeight (actualReadout S n sigma b + actualReadout S n tau b) := by
  have hs := Finset.card_le_card (actual_interval_support S n sigma tau a b ha)
  have hc := propagate_card S n b.val (Nat.le_of_lt_succ b.isLt) a ha
    (hammingSupport (actualReadout S n sigma b + actualReadout S n tau b))
  rw [rxCount_formula _ _ ha] at hc
  exact hs.trans hc
end QEC.Coding.BDL26HistorySyndromeSensitivity
