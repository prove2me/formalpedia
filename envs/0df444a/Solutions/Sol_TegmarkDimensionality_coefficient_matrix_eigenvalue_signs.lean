-- Prove2me | solution 1 for TegmarkDimensionality.coefficient_matrix_eigenvalue_signs
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T06:48:07.5853+00:00
-- url     : https://prove2.me/submissions/89ad90aa-fe97-4650-926a-47ca79813e1c

import Mathlib
import Definitions.Def_tegmark_pde_classification

set_option autoImplicit false

namespace Tegmark1fb02dd3Aux

open Matrix Polynomial

theorem charpoly_conj_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℝ)) (f : ι → ℝ) :
    ((U : Matrix ι ι ℝ) * diagonal f * star (U : Matrix ι ι ℝ)).charpoly
      = ∏ i, (X - C (f i)) := by
  rw [mul_assoc, Matrix.charpoly_mul_comm, mul_assoc, Unitary.coe_star_mul_self, mul_one,
    charpoly_diagonal]

theorem roots_conj_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℝ)) (f : ι → ℝ) :
    ((U : Matrix ι ι ℝ) * diagonal f * star (U : Matrix ι ι ℝ)).charpoly.roots
      = Multiset.map f Finset.univ.val := by
  rw [charpoly_conj_diag, Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

theorem conj_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℝ)) (e : ι → ℝ) (he : ∀ i, e i ≠ 0) :
    ((U : Matrix ι ι ℝ) * diagonal e * star (U : Matrix ι ι ℝ))⁻¹
      = (U : Matrix ι ι ℝ) * diagonal (fun i => (e i)⁻¹) * star (U : Matrix ι ι ℝ) := by
  apply Matrix.inv_eq_right_inv
  simp only [mul_assoc]
  rw [← mul_assoc (star (U : Matrix ι ι ℝ)) (U : Matrix ι ι ℝ), Unitary.coe_star_mul_self,
    one_mul, ← mul_assoc (diagonal e), diagonal_mul_diagonal]
  have : (fun i => e i * (e i)⁻¹) = fun _ => (1 : ℝ) := by
    funext i; exact mul_inv_cancel₀ (he i)
  rw [this, diagonal_one, one_mul]
  exact Unitary.mul_star_self_of_mem U.prop

theorem main_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℝ)) (e : ι → ℝ) (he : ∀ i, e i ≠ 0) :
    TegmarkDimensionality.numPosEigenvalues
        ((U : Matrix ι ι ℝ) * diagonal e * star (U : Matrix ι ι ℝ))⁻¹
      = TegmarkDimensionality.numPosEigenvalues
        ((U : Matrix ι ι ℝ) * diagonal e * star (U : Matrix ι ι ℝ)) ∧
    TegmarkDimensionality.numNegEigenvalues
        ((U : Matrix ι ι ℝ) * diagonal e * star (U : Matrix ι ι ℝ))⁻¹
      = TegmarkDimensionality.numNegEigenvalues
        ((U : Matrix ι ι ℝ) * diagonal e * star (U : Matrix ι ι ℝ)) := by
  rw [conj_inv U e he]
  unfold TegmarkDimensionality.numPosEigenvalues TegmarkDimensionality.numNegEigenvalues
  rw [roots_conj_diag, roots_conj_diag]
  simp [Multiset.filter_map, inv_pos]

end Tegmark1fb02dd3Aux

open TegmarkDimensionality Matrix in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Matrix ι ι ℝ) (hg : g.IsSymm) (hdet : g.det ≠ 0) :
    numPosEigenvalues g⁻¹ = numPosEigenvalues g ∧
      numNegEigenvalues g⁻¹ = numNegEigenvalues g := by
  have hH : g.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hg
  have hspec : g = (hH.eigenvectorUnitary : Matrix ι ι ℝ) * diagonal hH.eigenvalues
      * star (hH.eigenvectorUnitary : Matrix ι ι ℝ) := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa using h
  have he : ∀ i, hH.eigenvalues i ≠ 0 := by
    intro i hi
    apply hdet
    rw [hH.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have key := Tegmark1fb02dd3Aux.main_aux hH.eigenvectorUnitary hH.eigenvalues he
  rw [← hspec] at key
  exact key
