-- Prove2me | solution 1 for TroppMatrixConcentration.ch8_operator_jensen
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:48:26.610978+00:00
-- url     : https://prove2.me/submissions/c419e18d-811b-4c50-b35f-f6e2cf65112c

import Theorems.Thm_TroppMatrixConcentration_ch8_jensen_isometric_compression
import Theorems.Thm_TroppMatrixConcentration_ch8_jensen_block_calculus
import Mathlib.Data.Matrix.ColumnRowPartitioned

open scoped Matrix.Norms.L2Operator ComplexOrder

open TroppMatrixConcentration

theorem solution {d m n : ℕ} [NeZero d] [NeZero m] [NeZero n]
    (I : Set ℝ) (f : ℝ → ℝ) (hf : ch8_operatorConvexOn I f)
    (A₁ : Matrix (Fin m) (Fin m) ℂ) (A₂ : Matrix (Fin n) (Fin n) ℂ)
    (hA₁ : A₁.IsHermitian) (hA₂ : A₂.IsHermitian)
    (hA₁I : spectrum ℝ A₁ ⊆ I) (hA₂I : spectrum ℝ A₂ ⊆ I)
    (K₁ : Matrix (Fin m) (Fin d) ℂ) (K₂ : Matrix (Fin n) (Fin d) ℂ)
    (hK : K₁.conjTranspose * K₁ + K₂.conjTranspose * K₂ = 1) :
    loewnerLE
      (ch8_matrixFunction f (K₁.conjTranspose * A₁ * K₁ + K₂.conjTranspose * A₂ * K₂))
      (K₁.conjTranspose * ch8_matrixFunction f A₁ * K₁ +
        K₂.conjTranspose * ch8_matrixFunction f A₂ * K₂) := by
  obtain ⟨hAB, hspec, hcalc⟩ := ch8_jensen_block_calculus A₁ A₂ hA₁ hA₂ f
  have hdomain : spectrum ℝ (Matrix.fromBlocks A₁ 0 0 A₂) ⊆ I := by
    rw [hspec]
    exact Set.union_subset hA₁I hA₂I
  have hisometry : (Matrix.fromRows K₁ K₂).conjTranspose * Matrix.fromRows K₁ K₂ = 1 := by
    simpa only [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows] using hK
  have h := ch8_jensen_isometric_compression I f hf
    (Matrix.fromBlocks A₁ 0 0 A₂) hAB hdomain (Matrix.fromRows K₁ K₂) hisometry
  simpa only [hcalc, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows, Matrix.zero_mul,
    add_zero, zero_add, Matrix.fromCols_mul_fromRows] using h


