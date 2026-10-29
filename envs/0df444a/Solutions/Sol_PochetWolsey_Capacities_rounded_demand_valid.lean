-- Prove2me | solution 1 for PochetWolsey.Capacities.rounded_demand_valid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T03:23:41.758509+00:00
-- url     : https://prove2.me/submissions/455f7f23-530f-4f95-8940-0c6a5869fb11

import Mathlib
import Definitions.Def_PochetWolsey_Capacities_Model

theorem solution {n : ℕ} (hn : 0 < n) (C : ℝ) (hC : 0 < C)
    (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t ∧ d t ≤ C)
    (hfeas : ({y : Fin n → ℝ | (∀ u, y u = 0 ∨ y u = 1) ∧
      ∀ t, (∑ u ∈ Finset.Iic t, d u) ≤ C * ∑ u ∈ Finset.Iic t, y u} : Set _).Nonempty)
    (y : Fin n → ℝ) (hy : ∀ u, y u = 0 ∨ y u = 1)
    (hcover : ∀ t, (∑ u ∈ Finset.Iic t, d u) ≤ C * ∑ u ∈ Finset.Iic t, y u) :
    ∀ t, (⌈(∑ u ∈ Finset.Iic t, d u) / C⌉ : ℤ) ≤
      (∑ u ∈ Finset.Iic t, y u) := by
  classical
  intro t
  have hyn : ∀ u, y u = ((if y u = 1 then 1 else 0 : ℕ) : ℝ) := by
    intro u; rcases hy u with h | h <;> simp [h]
  have hsum : (∑ u ∈ Finset.Iic t, y u) =
      ((∑ u ∈ Finset.Iic t, (if y u = 1 then 1 else 0 : ℕ) : ℕ) : ℝ) := by
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl (fun u _ => hyn u)
  have h1 := hcover t
  rw [hsum] at h1 ⊢
  have h2 : (∑ u ∈ Finset.Iic t, d u) / C ≤
      (((∑ u ∈ Finset.Iic t, (if y u = 1 then 1 else 0 : ℕ) : ℕ) : ℤ) : ℝ) := by
    rw [Int.cast_natCast, div_le_iff₀ hC]; linarith
  have := Int.ceil_le.mpr h2
  exact_mod_cast this
