-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.actual_interval_contraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:46:12.453233+00:00
-- url     : https://prove2.me/submissions/f0023f94-a081-41af-9321-777924ec88a3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_prefix_contraction
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_interval


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26PairedHistoryQueryCone
theorem _root_.solution (s : TopInput S n) (a b : LevelIndex n)
    (ha : a.val ≤ b.val) :
    2 ^ rxCount a.val b.val * HammingWeight (actualInputs S n s a).val ≤
      HammingWeight (actualInputs S n s b).val := by
  rw [actualInputs_interval S n s b a ha]
  exact prefix_contraction S n b.val (Nat.le_of_lt_succ b.isLt) _ a ha
end QEC.Coding.BDL26PairedHistoryQueryCone
