-- Prove2me | solution 1 for Zeta9Note.min_lt_weighted_average_lt_max
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T08:24:00.110425+00:00
-- url     : https://prove2.me/submissions/590b79ef-1ee5-4e55-8460-b5256b11bd25

-- Public-mission submission for Zeta9Note.min_lt_weighted_average_lt_max.
-- Statement and proof verified in formalization/Zeta9Note.lean (exit 0, no placeholder).

import Mathlib

theorem solution
    (w r : Fin 5 → ℝ) (hw : ∀ j : Fin 5, 0 < w j)
    (hsum : ∑ j : Fin 5, w j = 1)
    (hnd : ∃ j j' : Fin 5, r j ≠ r j') :
    (∃ j : Fin 5, r j < ∑ i : Fin 5, w i * r i) ∧
      (∃ j : Fin 5, (∑ i : Fin 5, w i * r i) < r j) := by
  classical
  obtain ⟨j₁, j₂, hne⟩ := hnd
  have key_lower : ∀ c : ℝ, (∀ i : Fin 5, c ≤ r i) →
      (∑ i : Fin 5, w i * r i = c) → False := by
    intro c hc hval
    have hzero : ∑ i : Fin 5, w i * (r i - c) = 0 := by
      have hsplit : ∑ i : Fin 5, w i * (r i - c)
          = (∑ i : Fin 5, w i * r i) - (∑ i : Fin 5, w i * c) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsplit, hval, ← Finset.sum_mul, hsum, one_mul, sub_self]
    have hall : ∀ i : Fin 5, r i = c := by
      intro i
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => mul_nonneg (le_of_lt (hw i)) (sub_nonneg.mpr (hc i)))).mp hzero i
        (Finset.mem_univ i)
      exact sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hw i)))
    exact hne (by rw [hall j₁, hall j₂])
  have key_upper : ∀ c : ℝ, (∀ i : Fin 5, r i ≤ c) →
      (∑ i : Fin 5, w i * r i = c) → False := by
    intro c hc hval
    have hzero : ∑ i : Fin 5, w i * (c - r i) = 0 := by
      have hsplit : ∑ i : Fin 5, w i * (c - r i)
          = (∑ i : Fin 5, w i * c) - (∑ i : Fin 5, w i * r i) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsplit, ← Finset.sum_mul, hsum, one_mul, hval, sub_self]
    have hall : ∀ i : Fin 5, r i = c := by
      intro i
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => mul_nonneg (le_of_lt (hw i)) (sub_nonneg.mpr (hc i)))).mp hzero i
        (Finset.mem_univ i)
      exact (sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hw i)))).symm
    exact hne (by rw [hall j₁, hall j₂])
  constructor
  · by_contra h
    exact key_lower (∑ i : Fin 5, w i * r i)
      (fun i => not_lt.mp fun hi => h ⟨i, hi⟩) rfl
  · by_contra h
    exact key_upper (∑ i : Fin 5, w i * r i)
      (fun i => not_lt.mp fun hi => h ⟨i, hi⟩) rfl
