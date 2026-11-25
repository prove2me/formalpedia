-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombHookCount_proof_0ea3c888cea1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:51:45.045409+00:00
-- url     : https://prove2.me/submissions/7cb1682c-a56d-4b62-99e2-a5bc88c1bfce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Lattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombHookCount
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_card_latticeWords_zero_of_eq_zero_ae88b6fd3ba2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_zero_8589bd36c748
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_card_latticeWords_succ_572166936617


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset Comb
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CombHookCount
theorem _root_.solution (h1 : CombHookShapeFacts.Statement) (h2 : CombHookBranch.Statement) :
    CombHookCount.Statement := by
  intro r s
  induction s with
  | zero => intro l hl; omega
  | succ s ih =>
    intro l hl hsr
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · have hl0 : l = 0 := by omega
      subst hl0
      have hr : 0 < r := by omega
      rw [card_latticeWords_succ 0 _ (h1 r 1 0 (by omega) hsr).1,
        Finset.sum_eq_single (⟨0, hr⟩ : Fin r) ?_ (fun h => absurd (mem_univ _) h)]
      · rw [if_pos (by simp [hookShape]), card_latticeWords_zero_of_eq_zero _ (fun i => ?_)]
        · simp
        · by_cases hi : i = ⟨0, hr⟩
          · subst hi; simp [hookShape]
          · rw [Function.update_of_ne hi]
            have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
            simp [hookShape, this]
      · intro b _ hb
        have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
        rw [if_neg]
        simp [hookShape, this]
    · rw [card_latticeWords_succ s _ (h1 r (s + 1) l hl hsr).1,
        Finset.sum_congr rfl (fun a _ => h2 r s l hs (by omega) hsr a), Finset.sum_add_distrib,
        Finset.sum_eq_single (⟨0, by omega⟩ : Fin r)
          (fun b _ hb => if_neg (fun h => hb (Fin.ext h.1))) (fun h => absurd (mem_univ _) h),
        Finset.sum_eq_single (⟨l, by omega⟩ : Fin r)
          (fun b _ hb => if_neg (fun h => hb (Fin.ext h.1))) (fun h => absurd (mem_univ _) h)]
      simp only [true_and, Nat.add_sub_cancel]
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      rcases Nat.eq_zero_or_pos l with rfl | hl1
      · rw [if_pos hs, if_neg (by omega), ih 0 hs (by omega)]
        simp
      · obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
        rw [if_pos (show 1 ≤ k + 1 by omega), Nat.add_sub_cancel, ih k (by omega) (by omega),
          Nat.add_sub_cancel, Nat.choose_succ_succ]
        rcases Nat.lt_or_ge (k + 1) (t + 1) with hk | hk
        · rw [if_pos hk, ih (k + 1) hk (by omega), Nat.add_sub_cancel]
          ring
        · rw [if_neg (by omega), Nat.choose_eq_zero_of_lt (show t < k + 1 by omega)]
          ring
end CombHookCount
end GroundTheory.Heights₂.Heights.RestTerms
