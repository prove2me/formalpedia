-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.dot_rhoN_root_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:51.883866+00:00
-- url     : https://prove2.me/submissions/db1e1524-ee0b-4b54-9981-5a1bbadd225b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_numRho_dot_root_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_numRho_cardR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section NumRho
variable {ε : Fin n → Bool}
private theorem card_opposite_sign_above_add_below_eq (ε : Fin n → Bool) (x : Fin n) :
    ((univ.filter fun c => x < c ∧ ε c ≠ ε x).card : ℝ) +
      ((univ.filter fun c => c < x ∧ ε c ≠ ε x).card : ℝ) =
      ((univ.filter fun c => ε c ≠ ε x).card : ℝ) := by
  simp only [numRho_cardR]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rcases lt_trichotomy c x with h | h | h
  · simp [h, not_lt.mpr h.le]
  · subst h
    simp
  · simp [h, not_lt.mpr h.le]
end NumRho
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b) :
    2 - (n : ℝ) / 2 ≤ dot (rhoN ε) (root a b) := by
  rw [numRho_dot_root_right]
  have hA := card_opposite_sign_above_add_below_eq ε a
  have hB := card_opposite_sign_above_add_below_eq ε b
  have hsum : ((univ.filter fun c => ε c ≠ ε a).card : ℝ) +
      ((univ.filter fun c => ε c ≠ ε b).card : ℝ) = n := by
    simp only [numRho_cardR]
    rw [← Finset.sum_add_distrib]
    have hc : ∀ c : Fin n,
        ((if ε c ≠ ε a then (1:ℝ) else 0) + if ε c ≠ ε b then (1:ℝ) else 0) = 1 := by
      intro c
      cases h1 : ε c <;> cases h2 : ε a <;> cases h3 : ε b <;> simp_all
    simp only [hc]
    simp
  have hUa : (1:ℝ) ≤ ((univ.filter fun c => a < c ∧ ε c ≠ ε a).card : ℝ) := by
    have h : 0 < (univ.filter fun c => a < c ∧ ε c ≠ ε a).card :=
      Finset.card_pos.mpr ⟨b, by simp [hab, Ne.symm hε]⟩
    exact_mod_cast h
  have hLb : (1:ℝ) ≤ ((univ.filter fun c => c < b ∧ ε c ≠ ε b).card : ℝ) := by
    have h : 0 < (univ.filter fun c => c < b ∧ ε c ≠ ε b).card :=
      Finset.card_pos.mpr ⟨a, by simp [hab, hε]⟩
    exact_mod_cast h
  have hra : 2 * rhoN ε a = ((univ.filter fun c => a < c ∧ ε c ≠ ε a).card : ℝ) -
      ((univ.filter fun c => c < a ∧ ε c ≠ ε a).card : ℝ) := by
    simp only [rhoN]
    ring
  have hrb : 2 * rhoN ε b = ((univ.filter fun c => b < c ∧ ε c ≠ ε b).card : ℝ) -
      ((univ.filter fun c => c < b ∧ ε c ≠ ε b).card : ℝ) := by
    simp only [rhoN]
    ring
  linarith
end ReciprocityTheory.ChartRestriction.DS
