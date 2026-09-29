-- Prove2me | solution 1 for Zeta9Note.mediant_strictly_between_min_and_max
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T08:24:01.728846+00:00
-- url     : https://prove2.me/submissions/e6a13c32-82a5-4e04-aaae-024d319b6ef3

-- Public-mission submission for Zeta9Note.mediant_strictly_between_min_and_max.
-- Statement and proof verified in formalization/Zeta9Note.lean (exit 0, no placeholder).

import Mathlib
import Theorems.Thm_Zeta9Note_min_lt_weighted_average_lt_max

theorem solution
    (w a b : Fin 5 → ℝ)
    (hw : ∀ j : Fin 5, 0 < w j)
    (hb : ∀ j : Fin 5, 0 < b j)
    (hnd : ∃ j j' : Fin 5, a j / b j ≠ a j' / b j') :
    (∃ j : Fin 5,
        a j / b j < (∑ i : Fin 5, w i * a i) / (∑ i : Fin 5, w i * b i)) ∧
      (∃ j : Fin 5,
        (∑ i : Fin 5, w i * a i) / (∑ i : Fin 5, w i * b i) < a j / b j) := by
  classical
  set B : ℝ := ∑ i : Fin 5, w i * b i with hB
  have hBpos : 0 < B := by
    rw [hB]
    exact Finset.sum_pos' (fun i _ => mul_nonneg (le_of_lt (hw i)) (le_of_lt (hb i)))
      ⟨0, Finset.mem_univ 0, mul_pos (hw 0) (hb 0)⟩
  set v : Fin 5 → ℝ := fun j => w j * b j / B with hv
  have hvpos : ∀ j : Fin 5, 0 < v j := fun j => div_pos (mul_pos (hw j) (hb j)) hBpos
  have hvsum : ∑ j : Fin 5, v j = 1 := by
    have h1 : ∑ j : Fin 5, v j = B / B := by
      simp only [hv, div_eq_mul_inv, ← Finset.sum_mul, ← hB]
    rw [h1, div_self (ne_of_gt hBpos)]
  have hmediant : (∑ i : Fin 5, w i * a i) / B = ∑ j : Fin 5, v j * (a j / b j) := by
    have hterm : ∀ j : Fin 5, v j * (a j / b j) = (w j * a j) / B := by
      intro j
      have hBne : B ≠ 0 := ne_of_gt hBpos
      have hbj : b j ≠ 0 := ne_of_gt (hb j)
      simp only [hv]
      field_simp
      try ring
    have hsum : ∑ j : Fin 5, (w j * a j) / B = (∑ j : Fin 5, w j * a j) / B := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
    have h1 : ∑ j : Fin 5, v j * (a j / b j) = (∑ j : Fin 5, w j * a j) / B :=
      (Finset.sum_congr rfl fun j _ => hterm j).trans hsum
    exact h1.symm
  obtain ⟨hs1, hs2⟩ :=
    Zeta9Note.min_lt_weighted_average_lt_max v (fun j => a j / b j) hvpos hvsum hnd
  constructor
  · obtain ⟨j, hj⟩ := hs1
    exact ⟨j, by rw [hmediant]; exact hj⟩
  · obtain ⟨j, hj⟩ := hs2
    exact ⟨j, by rw [hmediant]; exact hj⟩
