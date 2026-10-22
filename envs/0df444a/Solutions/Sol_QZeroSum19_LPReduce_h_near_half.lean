-- Prove2me | solution 1 for QZeroSum19.LPReduce.h_near_half
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:21:57.883557+00:00
-- url     : https://prove2.me/submissions/1f02f052-b58d-4e1c-b799-32dcf2280ef7

import Mathlib
import Definitions.Def_QZeroSum19_LPReduce_Setting

set_option autoImplicit false
open Matrix
open QZeroSum19.LPReduce

theorem qz_row0 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R : ℝ) (y : Fin m ⊕ Fin 2 → ℝ) :
    (gameMatrix A b c α R *ᵥ y) (Sum.inl 0) = ∑ j, y (Sum.inl j) + y (Sum.inr 0) - y (Sum.inr 1) := by
  simp [gameMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem qz_row1 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R : ℝ) (y : Fin m ⊕ Fin 2 → ℝ) :
    (gameMatrix A b c α R *ᵥ y) (Sum.inl 1) = -∑ j, y (Sum.inl j) - y (Sum.inr 0) + y (Sum.inr 1) := by
  simp [gameMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem qz_row2 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R : ℝ) (y : Fin m ⊕ Fin 2 → ℝ) :
    (gameMatrix A b c α R *ᵥ y) (Sum.inr (Sum.inl ())) =
      -(b ⬝ᵥ (fun j => y (Sum.inl j))) + α / R * y (Sum.inr 1) := by
  simp [gameMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem qz_row3 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R : ℝ) (y : Fin m ⊕ Fin 2 → ℝ) (i : Fin n) :
    (gameMatrix A b c α R *ᵥ y) (Sum.inr (Sum.inr i)) =
      (A *ᵥ (fun j => y (Sum.inl j))) i - c i / R * y (Sum.inr 1) := by
  simp [gameMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem qz_simplex {m : ℕ} (y : Fin m ⊕ Fin 2 → ℝ) (hy : y ∈ stdSimplex ℝ (Fin m ⊕ Fin 2)) :
    (∀ j, 0 ≤ y (Sum.inl j)) ∧ 0 ≤ y (Sum.inr 0) ∧ 0 ≤ y (Sum.inr 1) ∧
      ∑ j, y (Sum.inl j) + y (Sum.inr 0) + y (Sum.inr 1) = 1 := by
  obtain ⟨h0, h1⟩ := hy
  refine ⟨fun j => h0 _, h0 _, h0 _, ?_⟩
  rw [Fintype.sum_sum_type, Fin.sum_univ_two] at h1
  linarith

theorem qz_h_half {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R κ : ℝ) (y' : Fin m ⊕ Fin 2 → ℝ) (hy' : y' ∈ stdSimplex ℝ (Fin m ⊕ Fin 2))
    (hle : ∀ k, (gameMatrix A b c α R *ᵥ y') k ≤ 2 * κ) :
    |y' (Sum.inr 1) - 1 / 2| ≤ κ := by
  obtain ⟨-, -, -, hs⟩ := qz_simplex y' hy'
  have h0 := hle (Sum.inl 0)
  have h1 := hle (Sum.inl 1)
  rw [qz_row0] at h0
  rw [qz_row1] at h1
  rw [abs_le]
  constructor <;> linarith

theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R κ : ℝ) (y' : Fin m ⊕ Fin 2 → ℝ) (hy' : y' ∈ stdSimplex ℝ (Fin m ⊕ Fin 2))
    (hle : ∀ k, (gameMatrix A b c α R *ᵥ y') k ≤ 2 * κ) :
    |y' (Sum.inr 1) - 1 / 2| ≤ κ := qz_h_half A b c α R κ y' hy' hle
