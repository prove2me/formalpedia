-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.directionalSaturationCounterexample
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:40:46.190075+00:00
-- url     : https://prove2.me/submissions/e4765359-28fe-469d-b329-11508e5d8103

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

def g52c_sg : Fin 3 → ℂ := ![1, 1, -1]

theorem g52c_sg_sq (i : Fin 3) : g52c_sg i * g52c_sg i = 1 := by
  fin_cases i <;> simp [g52c_sg]

theorem g52c_sign_conj (X : Mat 3) (i j : Fin 3) :
    (signMatrix * X * signMatrixᴴ) i j = g52c_sg i * X i j * g52c_sg j := by
  have hst : star g52c_sg = g52c_sg := by
    funext k; fin_cases k <;> simp [g52c_sg]
  simp only [signMatrix, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [show (star ![(1 : ℂ), 1, -1]) = g52c_sg from hst]
  rfl

theorem g52c_dm_apply (q : ℝ) (X : Mat 3) (i j : Fin 3) :
    directionalMixture q X i j = ((q : ℂ) + ((1 - q : ℝ) : ℂ) * (g52c_sg i * g52c_sg j)) * X i j := by
  simp only [directionalMixture, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, g52c_sign_conj]
  ring

end

end QAlgorithms.Papers.Independent.Information100.P44

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P44 in
open scoped ComplexConjugate ComplexOrder Matrix in
theorem solution (E0 E1 beta q : ℝ) (hE : E0 ≠ E1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    IsCGP ![E0,E1,E1] beta (directionalMixture q) ∧
    (∀ (X : Mat 3) i, directionalMixture q X i i = X i i) ∧
    directionalMixture q (matrixUnit 0 1) = matrixUnit 0 1 ∧
    directionalMixture q (matrixUnit 0 2) = ((2*q-1 : ℝ) : ℂ) • matrixUnit 0 2 ∧
    ‖directionalMixture q (matrixUnit 0 1) 0 1‖ =
      Real.sqrt (population (directionalMixture q) 0 0 * population (directionalMixture q) 1 1) ∧
    (q ≠ 1/2 → (shortModeMatrix q).rank = 2) := by
  have hdiag : ∀ (X : Mat 3) i, directionalMixture q X i i = X i i := by
    intro X i
    rw [g52c_dm_apply, g52c_sg_sq]; push_cast; ring
  have h01 : directionalMixture q (matrixUnit 0 1) = matrixUnit 0 1 := by
    ext i j
    rw [g52c_dm_apply]
    fin_cases i <;> fin_cases j <;> simp [matrixUnit, Matrix.single_apply, g52c_sg]
  have h02 : directionalMixture q (matrixUnit 0 2) = ((2*q-1 : ℝ) : ℂ) • matrixUnit 0 2 := by
    ext i j
    rw [g52c_dm_apply, Matrix.smul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp [matrixUnit, Matrix.single_apply, g52c_sg] <;> ring
  refine ⟨⟨?_, ?_, ?_⟩, hdiag, h01, h02, ?_, ?_⟩
  · -- channel: Kraus operators sqrt q • 1 and sqrt (1-q) • signMatrix
    have hq' : ((Real.sqrt q : ℝ) : ℂ) * ((Real.sqrt q : ℝ) : ℂ) = q := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hq0.le]
    have hq'' : ((Real.sqrt (1 - q) : ℝ) : ℂ) * ((Real.sqrt (1 - q) : ℝ) : ℂ) = ((1 - q : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
    have hSS : signMatrixᴴ * signMatrix = 1 := by
      ext i j
      have := g52c_sign_conj 1 i j
      simp only [signMatrix, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_apply, Matrix.one_apply]
      fin_cases i <;> fin_cases j <;> simp
    refine ⟨2, ![((Real.sqrt q : ℝ) : ℂ) • (1 : Mat 3), ((Real.sqrt (1 - q) : ℝ) : ℂ) • signMatrix],
      ?_, ?_⟩
    · simp only [IsKrausFamily, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, smul_smul, hSS, Complex.star_def, Complex.conj_ofReal, hq', hq'']
      rw [← add_smul]; push_cast; simp
    · intro X
      simp only [krausApply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, smul_smul, Complex.star_def, Complex.conj_ofReal, hq', hq'',
        directionalMixture]
  · intro t X
    ext i j
    simp only [g52c_dm_apply, timeEvolution]
    ring
  · ext i j
    rw [g52c_dm_apply]
    simp only [gibbsDensity, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rw [g52c_sg_sq]; push_cast; ring
    · ring
  · rw [h01]
    simp only [population, hdiag]
    simp [matrixUnit, Matrix.single_apply]
  · intro hq
    have hS : shortModeMatrix q = !![1, 0; 0, ((2 * q - 1 : ℝ) : ℂ)] := by
      ext i j
      simp only [shortModeMatrix]
      fin_cases i <;> fin_cases j <;> simp [g52c_dm_apply, matrixUnit, Matrix.single_apply, g52c_sg] <;> ring
    rw [hS]
    have hdet : (!![1, 0; 0, ((2 * q - 1 : ℝ) : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
      rw [Matrix.det_fin_two_of]
      simp only [one_mul, mul_zero, sub_zero]
      intro h0
      have : (2 * q - 1 : ℝ) = 0 := by exact_mod_cast h0
      exact hq (by linarith)
    rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin]
