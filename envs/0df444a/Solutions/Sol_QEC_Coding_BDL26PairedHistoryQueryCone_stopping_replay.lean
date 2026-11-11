-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.stopping_replay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:29:24.069239+00:00
-- url     : https://prove2.me/submissions/8ecd2665-4e77-4694-af1d-2f3923c7d380

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_potential_support
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_queries_self
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_query_agreement
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_binary_add_eq_zero_iff
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26PairedHistoryQueryCone
theorem _root_.solution (e : TopWord S n) (a : LevelIndex n) (ha : 0 < a.val)
    (s t : TopInput S n)
    (hs : actualInputs S n s a = actualInputs S n (perturbTop S n s e) a)
    (htop : AgreeOn (queries S n e a (TopIndex n)) s.val t.val)
    (hflip : AgreeOn (queries S n e a (TopIndex n))
      (perturbTop S n s e).val (perturbTop S n t e).val) :
    actualInputs S n t a = actualInputs S n (perturbTop S n t e) a := by
  apply Subtype.ext
  funext p
  by_cases hp : p ∈ potential S n e a
  · have hm : p ∈ queries S n e a a := by
      rw [queries_self,querySeed,if_neg (by omega)]
      exact hp
    exact (query_agreement S n e a s t htop a (Nat.le_refl _) p hm).symm.trans
      ((congrFun (congrArg Subtype.val hs) p).trans
        (query_agreement S n e a (perturbTop S n s e) (perturbTop S n t e)
          hflip a (Nat.le_refl _) p hm))
  · apply (binary_add_eq_zero_iff _ _).mp
    by_contra hn
    exact hp (potential_support S n t e a (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩))
end QEC.Coding.BDL26PairedHistoryQueryCone
