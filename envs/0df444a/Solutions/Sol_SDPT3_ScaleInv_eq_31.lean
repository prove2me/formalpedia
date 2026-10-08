-- Prove2me | solution 1 for SDPT3.ScaleInv.eq_31
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:20:28.345513+00:00
-- url     : https://prove2.me/submissions/73cf374d-85e8-4426-94a7-bbb4e1cae053

import Mathlib
import Definitions.Def_SDPT3_ScaleInv_Setting

open Matrix SDPT3.ScaleInv

private theorem jb_sq (k : ℕ) : Jbar k * Jbar k = 1 := by
  simp only [Jbar, diagonal_mul_diagonal]
  ext i j
  by_cases h : i = 0 <;> simp [h, diagonal_apply, Matrix.one_apply]

private theorem jb_trans (k : ℕ) : (Jbar k)ᵀ = Jbar k := by
  simp [Jbar]

theorem solution {k : ℕ} (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hF : Fᵀ * Jbar k * F = Jbar k) :
    IsUnit F.det ∧ Fᵀ * Jbar k = Jbar k * F⁻¹ ∧ Jbar k * F = (F⁻¹)ᵀ * Jbar k ∧
      Jbar k * Fᵀ = F⁻¹ * Jbar k := by
  have hl : (Jbar k * (Fᵀ * Jbar k)) * F = 1 := by
    rw [mul_assoc, hF, jb_sq]
  have hu := isUnit_det_of_left_inverse hl
  have hi : F⁻¹ = Jbar k * (Fᵀ * Jbar k) := by
    calc
      F⁻¹ = 1 * F⁻¹ := (one_mul _).symm
      _ = ((Jbar k * (Fᵀ * Jbar k)) * F) * F⁻¹ := by rw [hl]
      _ = Jbar k * (Fᵀ * Jbar k) := by rw [mul_assoc, mul_nonsing_inv F hu, mul_one]
  refine ⟨hu, ?_, ?_, ?_⟩
  · rw [hi, ← mul_assoc, jb_sq, one_mul]
  · rw [hi, transpose_mul, transpose_mul, jb_trans, transpose_transpose]
    simp only [mul_assoc, jb_sq, mul_one]
  · rw [hi, mul_assoc, mul_assoc, jb_sq, mul_one]

#print axioms solution
