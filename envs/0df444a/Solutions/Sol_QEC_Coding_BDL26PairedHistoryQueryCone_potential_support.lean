-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.potential_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:13:12.150226+00:00
-- url     : https://prove2.me/submissions/8abde55a-90cb-4552-92c9-033bb1865267

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_prefix_pair_support
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_binary_word_add_self


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26PairedHistoryQueryCone
theorem _root_.solution (s : TopInput S n) (e : TopWord S n) (a : LevelIndex n) :
    hammingSupport ((actualInputs S n s a).val +
      (actualInputs S n (perturbTop S n s e) a).val) ⊆ potential S n e a := by
  have ht : s.val + (perturbTop S n s e).val =
      (SuffixData S n).family.coboundary1 (TopIndex n) e := by
    change s.val + (s.val + _) = _
    rw [← add_assoc,binary_word_add_self,zero_add]
    change ((indexedFamily S (n+2)).coboundary1 (TopIndex (n+2))) e =
      ((indexedFamily S (n+2)).coboundary1 (LevelTwoHistory.physicalLevel (TopIndex n))) e
    rw [indexedFamily_coboundary1]
  have hs := prefix_pair_support S n n (Nat.le_refl _) s (perturbTop S n s e)
    a (Nat.le_of_lt_succ a.isLt)
  rw [ht] at hs
  exact hs
end QEC.Coding.BDL26PairedHistoryQueryCone
