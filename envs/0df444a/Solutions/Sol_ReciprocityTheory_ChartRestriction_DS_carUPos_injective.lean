-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.carUPos_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:41.668928+00:00
-- url     : https://prove2.me/submissions/9c9c3ba1-e309-4403-8d23-78d71c02f368

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_card_same_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_card_same_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) : Function.Injective (carUPos ε) := by
  have key : ∀ a a' : Fin n, a < a' → ε a = ε a' → carUPos ε a < carUPos ε a' := by
    intro a a' hlt he
    unfold carUPos
    rw [he]
    have hs : (univ.filter fun b => b < a ∧ ε b = ε a') ⊂ (univ.filter fun b => b < a' ∧ ε b = ε a') := by
      rw [ssubset_iff_of_subset]
      · exact ⟨a, by simp [hlt, he], by simp⟩
      · intro b hb
        simp only [mem_filter, mem_univ, true_and] at hb ⊢
        exact ⟨hb.1.trans hlt, hb.2⟩
    have := card_lt_card hs
    omega
  have key2 : ∀ a a' : Fin n, ε a = true → ε a' = false → carUPos ε a < carUPos ε a' := by
    intro a a' ha ha'
    have h1 := card_same_split ε a
    have h2 := card_same_eq ε a
    unfold carUPos
    simp only [ha, ha', Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢
    omega
  intro a a' hq
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · by_cases he : ε a = ε a'
    · exact (key a a' h he).ne hq
    · cases ha : ε a <;> cases ha' : ε a' <;> simp_all
      · exact (key2 a' a ha' ha).ne hq.symm
      · exact (key2 a a' ha ha').ne hq
  · by_cases he : ε a' = ε a
    · exact (key a' a h he).ne hq.symm
    · cases ha : ε a <;> cases ha' : ε a' <;> simp_all
      · exact (key2 a' a ha' ha).ne hq.symm
      · exact (key2 a a' ha ha').ne hq
end ReciprocityTheory.ChartRestriction.DS
