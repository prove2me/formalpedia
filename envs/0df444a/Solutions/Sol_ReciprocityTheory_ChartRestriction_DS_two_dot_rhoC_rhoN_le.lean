-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.two_dot_rhoC_rhoN_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:57.745212+00:00
-- url     : https://prove2.me/submissions/fe0fbbe1-26c8-461a-a28e-a9c1de1b6507

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_numRho_cardR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_numRho_sum_opp
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
theorem _root_.solution (ε : Fin n → Bool) :
    2 * dot (rhoC ε) (rhoN ε) ≤ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) := by
  have key : ∀ a : Fin n, 2 * (rhoC ε a * rhoN ε a) ≤
      (n : ℝ) / 2 * ((univ.filter fun c => ε c ≠ ε a).card : ℝ) := by
    intro a
    have hb := rhoC_bound ε a
    have hcn : ((univ.filter fun c => ε c = ε a).card : ℝ) ≤ n := by
      have h := Finset.card_filter_le (univ : Finset (Fin n)) (fun c => ε c = ε a)
      rw [Finset.card_univ, Fintype.card_fin] at h
      exact_mod_cast h
    have hs := card_opposite_sign_above_add_below_eq ε a
    have hr : 2 * rhoN ε a = ((univ.filter fun c => a < c ∧ ε c ≠ ε a).card : ℝ) -
        ((univ.filter fun c => c < a ∧ ε c ≠ ε a).card : ℝ) := by
      simp only [rhoN]
      ring
    have hU : (0:ℝ) ≤ ((univ.filter fun c => a < c ∧ ε c ≠ ε a).card : ℝ) := Nat.cast_nonneg _
    have hL : (0:ℝ) ≤ ((univ.filter fun c => c < a ∧ ε c ≠ ε a).card : ℝ) := Nat.cast_nonneg _
    have hC : |2 * rhoC ε a| ≤ (n : ℝ) := by linarith
    have hN : |2 * rhoN ε a| ≤ ((univ.filter fun c => ε c ≠ ε a).card : ℝ) := by
      rw [hr]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have he : (2 * rhoC ε a) * (2 * rhoN ε a) ≤ |2 * rhoC ε a| * |2 * rhoN ε a| := by
      rw [← abs_mul]
      exact le_abs_self _
    have hm : |2 * rhoC ε a| * |2 * rhoN ε a| ≤
        (n : ℝ) * ((univ.filter fun c => ε c ≠ ε a).card : ℝ) :=
      mul_le_mul hC hN (abs_nonneg _) (Nat.cast_nonneg n)
    have h4 : (2 * rhoC ε a) * (2 * rhoN ε a) = 4 * (rhoC ε a * rhoN ε a) := by ring
    have h5 : (n : ℝ) / 2 * ((univ.filter fun c => ε c ≠ ε a).card : ℝ) =
        ((n : ℝ) * ((univ.filter fun c => ε c ≠ ε a).card : ℝ)) / 2 := by ring
    linarith
  rw [dot, Finset.mul_sum]
  calc ∑ a, 2 * (rhoC ε a * rhoN ε a)
      ≤ ∑ a, (n : ℝ) / 2 * ((univ.filter fun c => ε c ≠ ε a).card : ℝ) :=
        Finset.sum_le_sum (fun a _ => key a)
    _ = (n : ℝ) / 2 * ∑ a, ((univ.filter fun c => ε c ≠ ε a).card : ℝ) := by
        rw [Finset.mul_sum]
    _ = (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) := by
        rw [numRho_sum_opp]
        ring
end ReciprocityTheory.ChartRestriction.DS
