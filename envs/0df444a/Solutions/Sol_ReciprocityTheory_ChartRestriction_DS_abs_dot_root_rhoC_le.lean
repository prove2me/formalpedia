-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.abs_dot_root_rhoC_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:20:34.733827+00:00
-- url     : https://prove2.me/submissions/1449648d-ae74-45d6-8997-4d3ae91dd32f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_numRho_dot_root_left
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
private theorem rhoC_bound (ε : Fin n → Bool) (a : Fin n) :
    |2 * rhoC ε a| + 1 ≤ ((univ.filter fun c => ε c = ε a).card : ℝ) := by
  have h2 : 2 * rhoC ε a = ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) -
      ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) := by
    simp only [rhoC]
    ring
  have hU : (0:ℝ) ≤ ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) := Nat.cast_nonneg _
  have hL : (0:ℝ) ≤ ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) := Nat.cast_nonneg _
  have key : ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) +
      ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) + 1 ≤
      ((univ.filter fun c => ε c = ε a).card : ℝ) := by
    have h1 : ∑ c : Fin n, (if c = a then (1:ℝ) else 0) = 1 := by simp
    rw [← h1]
    simp only [numRho_cardR]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro c _
    rcases lt_trichotomy c a with h | h | h
    · simp [h, not_lt.mpr h.le, h.ne]
    · subst h
      simp
    · simp [h, not_lt.mpr h.le, h.ne']
  rw [h2]
  have habs : |((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) -
      ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ)| ≤
      ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) +
      ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  linarith
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
theorem _root_.solution {a b : Fin n} (hε : ε a ≠ ε b) :
    |dot (root a b) (rhoC ε)| ≤ ((n : ℝ) - 2) / 2 := by
  rw [numRho_dot_root_left]
  have ha := rhoC_bound ε a
  have hb := rhoC_bound ε b
  have hsum : ((univ.filter fun c => ε c = ε a).card : ℝ) +
      ((univ.filter fun c => ε c = ε b).card : ℝ) = n := by
    simp only [numRho_cardR]
    rw [← Finset.sum_add_distrib]
    have hc : ∀ c : Fin n,
        ((if ε c = ε a then (1:ℝ) else 0) + if ε c = ε b then (1:ℝ) else 0) = 1 := by
      intro c
      cases h1 : ε c <;> cases h2 : ε a <;> cases h3 : ε b <;> simp_all
    simp only [hc]
    simp
  rw [abs_le]
  constructor <;> linarith [le_abs_self (2 * rhoC ε a), neg_abs_le (2 * rhoC ε a),
    le_abs_self (2 * rhoC ε b), neg_abs_le (2 * rhoC ε b)]
end ReciprocityTheory.ChartRestriction.DS
