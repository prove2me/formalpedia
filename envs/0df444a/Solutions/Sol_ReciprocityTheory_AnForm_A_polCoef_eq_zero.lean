-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.polCoef_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:42.59782+00:00
-- url     : https://prove2.me/submissions/b777dc7f-c37a-4428-b561-4d5ab1385090

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} (r : Fin D → Fin D) (h : ¬ Function.Surjective r) :
    polCoef r = 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, ∀ i, r i ≠ a := by
    simp only [Function.Surjective, not_forall, not_exists] at h
    obtain ⟨a, ha⟩ := h
    exact ⟨a, fun i hi => ha i hi⟩
  let t : Finset (Fin D) → Finset (Fin D) := fun S => if a ∈ S then S.erase a else insert a S
  have ht : Function.Involutive t := by
    intro S; by_cases hS : a ∈ S <;> simp [t, hS]
  let f : Finset (Fin D) → ℂ := fun S =>
    (-1 : ℂ) ^ (D - S.card) * if (∀ i, r i ∈ S) then 1 else 0
  have hmem : ∀ S, (∀ i, r i ∈ t S) ↔ ∀ i, r i ∈ S := by
    intro S
    by_cases hS : a ∈ S <;> simp [t, hS, ha]
  have key : ∀ S, f (t S) = - f S := by
    intro S
    simp only [f, hmem]
    by_cases hS : a ∈ S
    · have h1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨a, hS⟩
      have h2 : S.card ≤ D := by simpa using Finset.card_le_univ S
      have hc : (t S).card = S.card - 1 := by simp [t, hS, Finset.card_erase_of_mem]
      rw [hc, show D - (S.card - 1) = (D - S.card) + 1 by omega, pow_succ]
      ring
    · have h2 : (t S).card ≤ D := by simpa using Finset.card_le_univ (t S)
      have hc : (t S).card = S.card + 1 := by simp [t, hS]
      rw [hc] at h2
      rw [hc]
      rw [show D - S.card = (D - (S.card + 1)) + 1 by omega, pow_succ]
      ring
  have hsum : ∑ S, f S = ∑ S, f (ht.toPerm t S) := (Equiv.sum_comp (ht.toPerm t) f).symm
  simp only [Function.Involutive.coe_toPerm, key, Finset.sum_neg_distrib] at hsum
  have : ∑ S, f S = 0 := by linear_combination hsum / 2
  exact this
end ReciprocityTheory.AnForm.A
