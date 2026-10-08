-- Prove2me | solution 1 for VBSDP.Duality.trace_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:41:55.094987+00:00
-- url     : https://prove2.me/submissions/bcfc59c1-6932-414f-84bc-4f816b71e490

import Mathlib.Analysis.Matrix.Order
open scoped Matrix MatrixOrder

theorem solution {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (htr : (A * B).trace = 0) :
    A * B = 0 := by
  obtain ⟨a, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  have hz : a * bᴴ = 0 := by
    apply Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp
    calc
      (a * bᴴ * (a * bᴴ)ᴴ).trace = (star a * a * (star b * b)).trace := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.star_eq_conjTranspose]
        rw [← Matrix.mul_assoc (a * bᴴ) b aᴴ, Matrix.trace_mul_cycle]
        simp only [Matrix.mul_assoc]
      _ = 0 := htr
  calc
    star a * a * (star b * b) = star a * (a * bᴴ) * b := by
      simp only [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    _ = 0 := by rw [hz]; simp

#print axioms solution
