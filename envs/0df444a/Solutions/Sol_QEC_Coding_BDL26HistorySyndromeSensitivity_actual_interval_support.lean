-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.actual_interval_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:22:17.59175+00:00
-- url     : https://prove2.me/submissions/feb87b30-4a30-4466-8e45-135447ad4a78

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_prefix_pair_support
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_interval
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_readout


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
    hammingSupport (actualReadout S n sigma a + actualReadout S n tau a) ⊆
      propagate S n b.val (Nat.le_of_lt_succ b.isLt) a ha
        (hammingSupport (actualReadout S n sigma b + actualReadout S n tau b)) := by
  rw [actualInputs_readout, actualInputs_readout, actualInputs_readout, actualInputs_readout]
  rw [actualInputs_interval S n sigma b a ha, actualInputs_interval S n tau b a ha]
  exact prefix_pair_support S n b.val (Nat.le_of_lt_succ b.isLt) _ _ a ha
end QEC.Coding.BDL26HistorySyndromeSensitivity
