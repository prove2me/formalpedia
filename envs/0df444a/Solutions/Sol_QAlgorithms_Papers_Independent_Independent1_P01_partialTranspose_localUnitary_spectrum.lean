-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P01.partialTranspose_localUnitary_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:56:56.00691+00:00
-- url     : https://prove2.me/submissions/e4618a75-e003-4f2e-b9b3-a12903d5d79d

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P01_Model
set_option autoImplicit false

/-!
# Peres: Separability Criterion for Density Matrices

Source: arXiv:quant-ph/9604005v2, PDF pp.2–5. The first subsystem alone
is transposed, without complex conjugation. Equation (5), which has a
conjugating-factor defect, is deferred; its valid spectral conclusion is stated.
-/

noncomputable section

open scoped Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P01
open QAlgorithms.Entanglement

/-- Peres PDF pp.2–3, prose preceding Eqs. (4)–(5): arbitrary separate local
unitaries preserve the partial-transpose spectrum, including multiplicities.
This does not assert the defective printed covariance formula (5). -/


theorem solution
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J]
    (rho : Matrix (I × J) (I × J) ℂ) (density : IsDensityMatrix rho)
    (U : Matrix.unitaryGroup I ℂ) (V : Matrix.unitaryGroup J ℂ) :
    (partialTransposeFirst
      (conjSuperop (Matrix.kronecker (U : Matrix I I ℂ) (V : Matrix J J ℂ)) rho)).charpoly =
      (partialTransposeFirst rho).charpoly := by
  set W : Matrix (I × J) (I × J) ℂ :=
    Matrix.kronecker ((U : Matrix I I ℂ)ᴴ)ᵀ (V : Matrix J J ℂ) with hW
  have key : partialTransposeFirst
      (conjSuperop (Matrix.kronecker (U : Matrix I I ℂ) (V : Matrix J J ℂ)) rho) =
      W * partialTransposeFirst rho * Wᴴ := by
    ext p q
    simp only [hW, partialTransposeFirst, conjSuperop, Matrix.mul_apply, Matrix.of_apply,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Finset.sum_mul, star_mul', star_star]
    conv_rhs => enter [2, x]; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    conv_rhs => enter [2, y]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hU : (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ) = 1 := Matrix.UnitaryGroup.star_mul_self U
  have hV : (V : Matrix J J ℂ)ᴴ * (V : Matrix J J ℂ) = 1 := Matrix.UnitaryGroup.star_mul_self V
  have hWW : Wᴴ * W = 1 := by
    rw [hW]; unfold Matrix.kronecker
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_transpose,
      show ((U : Matrix I I ℂ).map star)ᴴ = (U : Matrix I I ℂ)ᵀ from by ext; simp,
      show (U : Matrix I I ℂ).map star = (U : Matrix I I ℂ)ᴴᵀ from by ext; simp,
      ← Matrix.transpose_mul, hU, hV, Matrix.transpose_one,
      Matrix.one_kronecker_one]
  rw [key, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hWW, Matrix.one_mul]

