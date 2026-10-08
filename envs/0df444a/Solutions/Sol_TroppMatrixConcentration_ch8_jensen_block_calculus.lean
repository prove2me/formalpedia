-- Prove2me | solution 1 for TroppMatrixConcentration.ch8_jensen_block_calculus
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:48:24.768634+00:00
-- url     : https://prove2.me/submissions/d9c720ed-7a4a-495b-90d6-de75464d4d89

import Definitions.Def_TroppMatrixConcentration_ch8_entropy
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped Matrix.Norms.L2Operator ComplexOrder
open TroppMatrixConcentration

private def blockHom
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] :
    (Matrix ι ι ℂ × Matrix κ κ ℂ) →⋆ₐ[ℂ] Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ where
  toFun p := Matrix.fromBlocks p.1 0 0 p.2
  map_one' := Matrix.fromBlocks_one
  map_mul' p q := by simp [Matrix.fromBlocks_multiply]
  map_zero' := Matrix.fromBlocks_zero
  map_add' p q := by ext i j; cases i <;> cases j <;> simp [Matrix.fromBlocks]
  commutes' r := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.algebraMap_eq_diagonal, Matrix.fromBlocks, Matrix.diagonal]
  map_star' p := by simp [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]

theorem solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) :
    (Matrix.fromBlocks A 0 0 B).IsHermitian ∧
    spectrum ℝ (Matrix.fromBlocks A 0 0 B) = spectrum ℝ A ∪ spectrum ℝ B ∧
    ch8_matrixFunction f (Matrix.fromBlocks A 0 0 B) =
      Matrix.fromBlocks (ch8_matrixFunction f A) 0 0 (ch8_matrixFunction f B) := by
  have hblock := hA.fromBlocks (B := (0 : Matrix ι κ ℂ)) (C := 0) (by simp) hB
  refine ⟨hblock, ?_, ?_⟩
  · ext r
    have heq : algebraMap ℝ (Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) r -
        Matrix.fromBlocks A 0 0 B =
        Matrix.fromBlocks (algebraMap ℝ (Matrix ι ι ℂ) r - A) 0 0
          (algebraMap ℝ (Matrix κ κ ℂ) r - B) := by
      ext i j
      cases i <;> cases j <;> simp [Matrix.algebraMap_eq_diagonal, Matrix.fromBlocks, Matrix.diagonal]
    simp only [Set.mem_union, spectrum.mem_iff, heq, Matrix.isUnit_iff_isUnit_det,
      Matrix.det_fromBlocks_zero₂₁, isUnit_iff_ne_zero, mul_ne_zero_iff, not_and_or]
  · letI : ContinuousFunctionalCalculus ℝ (Matrix ι ι ℂ × Matrix κ κ ℂ) IsSelfAdjoint := by
      convert IsSelfAdjoint.instContinuousFunctionalCalculus (A := Matrix ι ι ℂ × Matrix κ κ ℂ) using 1
      apply Algebra.algebra_ext
      intro r
      rfl
    have hf : ContinuousOn f (spectrum ℝ A ∪ spectrum ℝ B) := by
      rw [hA.spectrum_real_eq_range_eigenvalues, hB.spectrum_real_eq_range_eigenvalues]
      exact ((Set.finite_range _).union (Set.finite_range _)).continuousOn f
    have hab : IsSelfAdjoint (A, B) := by exact Prod.ext hA hB
    have hm := (blockHom (ι := ι) (κ := κ)).map_cfc (R := ℝ) f (A, B)
      (by simpa only [Prod.spectrum_eq] using hf)
      (blockHom.toAlgHom.toLinearMap.continuous_of_finiteDimensional) hab hblock
    rw [cfc_map_prod (S := ℂ) f A B hf hab hA hB] at hm
    exact hm.symm
