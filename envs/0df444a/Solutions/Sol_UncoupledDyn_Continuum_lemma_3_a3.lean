-- Prove2me | solution 1 for UncoupledDyn.Continuum.lemma_3_a3
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:23:43.822661+00:00
-- url     : https://prove2.me/submissions/283e2f3c-a060-4818-bf09-746e123ba6cf

import Mathlib
import Definitions.Def_UncoupledDyn_Continuum_Setting

open UncoupledDyn.Continuum Polynomial Matrix

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

theorem solution (J1 J2 : Matrix (Fin 2) (Fin 2) ℝ) :
    (blockJ J1 J2).charpoly.coeff 1 = 3 * J1.det * J2.trace + 3 * J2.det * J1.trace := by
  classical
  rw [← Matrix.charpoly_reindex finProdFinEquiv]
  unfold Matrix.charpoly
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_zero,
    Matrix.submatrix_apply, Matrix.charmatrix_apply, Matrix.reindex_apply,
    Matrix.map_apply, Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  norm_num [blockJ, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.succAbove, Fin.lt_def, Matrix.det_fin_two, Matrix.trace, Matrix.diag,
    Fin.sum_univ_two, Matrix.of_apply]
  ring_nf
  simp [← Polynomial.C_pow, -map_pow, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.mul_coeff_one,
    Polynomial.mul_coeff_zero, Polynomial.coeff_X_pow]
  ring

#print axioms solution
