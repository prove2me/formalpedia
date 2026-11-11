-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.potential_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:28:58.038817+00:00
-- url     : https://prove2.me/submissions/80f60293-63e3-409c-b86f-7470adcd9e59

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_propagate_card
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_rxCount_formula
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26PairedHistoryQueryCone
theorem _root_.solution (e : TopWord S n) (a : LevelIndex n) :
    (potential S n e a).card ≤ 57 ^ (n-a.val) *
      HammingWeight ((SuffixData S n).family.coboundary1 (TopIndex n) e) := by
  have hc := propagate_card S n n (Nat.le_refl _) a (Nat.le_of_lt_succ a.isLt)
    (hammingSupport ((SuffixData S n).family.coboundary1 (TopIndex n) e))
  have hr : rxCount a.val n ≤ n-a.val := by
    rw [rxCount_formula _ _ (Nat.le_of_lt_succ a.isLt)]
    omega
  exact hc.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hr))
end QEC.Coding.BDL26PairedHistoryQueryCone
