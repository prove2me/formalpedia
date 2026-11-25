-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.lowK_int_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:32:30.122377+00:00
-- url     : https://prove2.me/submissions/49878f2a-35ac-4b3e-8377-d586376d7132

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HcParamGapGeIndex
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_hc_param_gap_ge_index
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lowest_k_type_formula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) (lam : Fin n → ℝ) (hlam : IsHCParam lam) :
    (∀ a, ∃ m : ℤ, lowK ε lam a = m) ∧ ∀ a b, a < b → ε a = ε b → lowK ε lam b ≤ lowK ε lam a := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · obtain ⟨m, hm⟩ := hlam.2 a
    refine ⟨m + (n : ℤ) - 1 - ((a : ℕ) : ℤ) - ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℤ)
      + ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℤ), ?_⟩
    rw [lowest_k_type_formula]
    push_cast
    linarith
  · have hs : ε b = ε a := he.symm
    have hab' : (a : ℕ) ≤ b := le_of_lt (Fin.lt_def.mp hab)

    have c1 : (univ.filter fun c => a < c ∧ ε c = ε a).card ≤
        (univ.filter fun c => b < c ∧ ε c = ε b).card + ((b : ℕ) - a) := by
      calc _ ≤ ((univ.filter fun c => b < c ∧ ε c = ε b) ∪ Finset.Ioc a b).card := by
            apply Finset.card_le_card
            intro c hc
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
              Finset.mem_Ioc] at hc ⊢
            rw [hs]
            by_cases hcb : b < c
            · exact Or.inl ⟨hcb, hc.2⟩
            · exact Or.inr ⟨hc.1, not_lt.mp hcb⟩
        _ ≤ _ := by
            rw [← Fin.card_Ioc]
            exact Finset.card_union_le _ _
    have c2 : (univ.filter fun c => c < b ∧ ε c = ε b).card ≤
        (univ.filter fun c => c < a ∧ ε c = ε a).card + ((b : ℕ) - a) := by
      calc _ ≤ ((univ.filter fun c => c < a ∧ ε c = ε a) ∪ Finset.Ico a b).card := by
            apply Finset.card_le_card
            intro c hc
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
              Finset.mem_Ico] at hc ⊢
            rw [← hs]
            by_cases hca : c < a
            · exact Or.inl ⟨hca, hc.2⟩
            · exact Or.inr ⟨not_lt.mp hca, hc.1⟩
        _ ≤ _ := by
            rw [← Fin.card_Ico]
            exact Finset.card_union_le _ _
    have gap := hc_param_gap_ge_index lam hlam a b hab.le
    have c1r : (((univ.filter fun c => a < c ∧ ε c = ε a).card : ℕ) : ℝ) ≤
        ((univ.filter fun c => b < c ∧ ε c = ε b).card : ℕ) + (((b : ℕ) : ℝ) - (a : ℕ)) := by
      have := c1
      rw [← Nat.cast_le (α := ℝ)] at this
      push_cast [Nat.cast_sub hab'] at this
      linarith
    have hcard₃ : (((univ.filter fun c => c < b ∧ ε c = ε b).card : ℕ) : ℝ) ≤
        ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℕ) + (((b : ℕ) : ℝ) - (a : ℕ)) := by
      have := c2
      rw [← Nat.cast_le (α := ℝ)] at this
      push_cast [Nat.cast_sub hab'] at this
      linarith
    rw [lowest_k_type_formula, lowest_k_type_formula]
    linarith
end ReciprocityTheory.ChartRestriction.DS.HW
