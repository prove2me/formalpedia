-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P09.tableBasisComplete
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:01:46.078998+00:00
-- url     : https://prove2.me/submissions/0d6b90ce-f61a-401e-9143-62aa141121c1

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
noncomputable section
open scoped Matrix ComplexOrder NNReal ENNReal
open QAlgorithms QAlgorithms.ErrorMitigation QAlgorithms.Papers.Independent.Independent1.P09

-- The rational certificate is checked by Lean's kernel and then mapped to ℝ.
private def flatQ : Matrix (Fin 16) (Fin 16) ℚ :=
  ![![1,1,1,1,1,1,1,1,1,1,1/2,1/2,1/2,1/2,1/2,1/2],
  ![0,0,0,0,0,0,0,0,0,0,1/2,0,0,1/2,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,1/2,0,0,1/2,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0,1/2,0,0,1/2],
  ![0,0,0,0,0,0,0,0,0,0,1/2,0,0,-1/2,0,0],
  ![1,1,-1,-1,1,0,0,-1,0,0,1/2,0,0,-1/2,0,0],
  ![0,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0],
  ![0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,1/2,0,0,-1/2,0],
  ![0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0],
  ![1,-1,1,-1,0,1,0,0,-1,0,0,1/2,0,0,-1/2,0],
  ![0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0,1/2,0,0,-1/2],
  ![0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0],
  ![0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0],
  ![1,-1,-1,1,0,0,1,0,0,-1,0,0,1/2,0,0,-1/2]]

private def inverseQ : Matrix (Fin 16) (Fin 16) ℚ :=
  ![![1/4,-1/4,-1/4,-1/4,-1/4,1/4,1/4,-1/4,-1/4,-1/4,1/4,1/4,-1/4,1/4,-1/4,1/4],
  ![1/4,-1/4,-1/4,-1/4,-1/4,1/4,-1/4,-1/4,1/4,-1/4,-1/4,1/4,1/4,-1/4,-1/4,-1/4],
  ![1/4,-1/4,-1/4,-1/4,1/4,-1/4,-1/4,-1/4,-1/4,-1/4,1/4,-1/4,1/4,1/4,-1/4,-1/4],
  ![1/4,-1/4,-1/4,-1/4,1/4,-1/4,1/4,-1/4,1/4,-1/4,-1/4,-1/4,-1/4,-1/4,-1/4,1/4],
  ![0,0,0,0,0,0,0,0,0,0,0,-1/2,0,0,1/2,0],
  ![0,0,0,0,0,0,0,1/2,0,0,0,0,0,-1/2,0,0],
  ![0,0,0,0,0,0,-1/2,0,0,1/2,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,1/2,0,0,1/2,0],
  ![0,0,0,0,0,0,0,1/2,0,0,0,0,0,1/2,0,0],
  ![0,0,0,0,0,0,1/2,0,0,1/2,0,0,0,0,0,0],
  ![0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0],
  ![0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0],
  ![0,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,1,0,0,0,0,0,-1,0,0,0,0,0,0,0],
  ![0,0,0,1,0,0,0,0,0,0,0,0,-1,0,0,0]]

private def computedFlat : Matrix (Fin 16) (Fin 16) ℝ := flatQ.map (Rat.castHom ℝ)
private def computedInverse : Matrix (Fin 16) (Fin 16) ℝ := inverseQ.map (Rat.castHom ℝ)

private lemma computed_inverse : computedFlat * computedInverse = 1 := by
  have hq : flatQ * inverseQ = 1 := by decide +kernel
  calc
    computedFlat * computedInverse = (flatQ * inverseQ).map (Rat.castHom ℝ) :=
      Matrix.map_mul.symm
    _ = (1 : Matrix (Fin 16) (Fin 16) ℚ).map (Rat.castHom ℝ) :=
      congrArg (fun M : Matrix (Fin 16) (Fin 16) ℚ => M.map (Rat.castHom ℝ)) hq
    _ = 1 := Matrix.map_one _ (map_zero _) (map_one _)

private lemma sqrt_mul_two : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

private lemma flat_row_0 (i : Fin 16) :
    localFlat localTransfer 0 i = computedFlat 0 i := by
  fin_cases i
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (1 : Matrix Bool Bool ℂ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      pauliX) (1 : Matrix Bool Bool ℂ)).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      pauliY) (1 : Matrix Bool Bool ℂ)).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      pauliZ) (1 : Matrix Bool Bool ℂ)).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliX)) (1 : Matrix Bool Bool ℂ)).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliY)) (1 : Matrix Bool Bool ℂ)).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliZ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliY+pauliZ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliZ+pauliX)) (1 : Matrix Bool Bool ℂ)).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliX+pauliY)) (1 : Matrix Bool Bool ℂ)).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliX)) (1 : Matrix Bool Bool ℂ)).trace.re = ((1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliY)) (1 : Matrix Bool Bool ℂ)).trace.re = ((1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliZ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliY+Complex.I • pauliZ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliZ+Complex.I • pauliX)) (1 : Matrix Bool Bool ℂ)).trace.re = ((1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliX+Complex.I • pauliY)) (1 : Matrix Bool Bool ℂ)).trace.re = ((1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma flat_row_1 (i : Fin 16) :
    localFlat localTransfer 1 i = computedFlat 1 i := by
  fin_cases i
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (1 : Matrix Bool Bool ℂ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      pauliX) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      pauliY) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      pauliZ) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliX)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliY)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliZ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliY+pauliZ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliZ+pauliX)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliX+pauliY)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliX)) (1 : Matrix Bool Bool ℂ)).trace.re = ((1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliY)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliZ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliY+Complex.I • pauliZ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliZ+Complex.I • pauliX)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliX+Complex.I • pauliY)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma flat_row_2 (i : Fin 16) :
    localFlat localTransfer 2 i = computedFlat 2 i := by
  fin_cases i
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (1 : Matrix Bool Bool ℂ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      pauliX) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      pauliY) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      pauliZ) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliX)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliY)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliZ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliY+pauliZ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliZ+pauliX)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliX+pauliY)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliX)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliY)) (1 : Matrix Bool Bool ℂ)).trace.re = ((1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliZ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliY+Complex.I • pauliZ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliZ+Complex.I • pauliX)) (1 : Matrix Bool Bool ℂ)).trace.re = ((1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliX+Complex.I • pauliY)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma flat_row_3 (i : Fin 16) :
    localFlat localTransfer 3 i = computedFlat 3 i := by
  fin_cases i
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (1 : Matrix Bool Bool ℂ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      pauliX) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      pauliY) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      pauliZ) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliX)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliY)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliZ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliY+pauliZ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliZ+pauliX)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliX+pauliY)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliX)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliY)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliZ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliY+Complex.I • pauliZ)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliZ+Complex.I • pauliX)) (1 : Matrix Bool Bool ℂ)).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliX+Complex.I • pauliY)) (1 : Matrix Bool Bool ℂ)).trace.re = ((1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma flat_row_4 (i : Fin 16) :
    localFlat localTransfer 4 i = computedFlat 4 i := by
  fin_cases i
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (1 : Matrix Bool Bool ℂ)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      pauliX) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      pauliY) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      pauliZ) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliX)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliY)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliZ)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliY+pauliZ)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliZ+pauliX)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliX+pauliY)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliX)) pauliX).trace.re = ((1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliY)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliZ)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliY+Complex.I • pauliZ)) pauliX).trace.re = ((-1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliZ+Complex.I • pauliX)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliX+Complex.I • pauliY)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma flat_row_5 (i : Fin 16) :
    localFlat localTransfer 5 i = computedFlat 5 i := by
  fin_cases i
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (1 : Matrix Bool Bool ℂ)) pauliX).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      pauliX) pauliX).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      pauliY) pauliX).trace.re = ((-1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      pauliZ) pauliX).trace.re = ((-1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliX)) pauliX).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliY)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliZ)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliY+pauliZ)) pauliX).trace.re = ((-1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliZ+pauliX)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliX+pauliY)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliX)) pauliX).trace.re = ((1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliY)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliZ)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliY+Complex.I • pauliZ)) pauliX).trace.re = ((-1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliZ+Complex.I • pauliX)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliX+Complex.I • pauliY)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma flat_row_6 (i : Fin 16) :
    localFlat localTransfer 6 i = computedFlat 6 i := by
  fin_cases i
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (1 : Matrix Bool Bool ℂ)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      pauliX) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      pauliY) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      pauliZ) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliX)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliY)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliZ)) pauliX).trace.re = ((-1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliY+pauliZ)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliZ+pauliX)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliX+pauliY)) pauliX).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliX)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliY)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliZ)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliY+Complex.I • pauliZ)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliZ+Complex.I • pauliX)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliX+Complex.I • pauliY)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma flat_row_7 (i : Fin 16) :
    localFlat localTransfer 7 i = computedFlat 7 i := by
  fin_cases i
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (1 : Matrix Bool Bool ℂ)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      pauliX) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      pauliY) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      pauliZ) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliX)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliY)) pauliX).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliZ)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliY+pauliZ)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliZ+pauliX)) pauliX).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliX+pauliY)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliX)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliY)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliZ)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliY+Complex.I • pauliZ)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliZ+Complex.I • pauliX)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliX+Complex.I • pauliY)) pauliX).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma flat_row_8 (i : Fin 16) :
    localFlat localTransfer 8 i = computedFlat 8 i := by
  fin_cases i
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (1 : Matrix Bool Bool ℂ)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      pauliX) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      pauliY) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      pauliZ) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliX)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliY)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliZ)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliY+pauliZ)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliZ+pauliX)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliX+pauliY)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliX)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliY)) pauliY).trace.re = ((1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliZ)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliY+Complex.I • pauliZ)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliZ+Complex.I • pauliX)) pauliY).trace.re = ((-1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliX+Complex.I • pauliY)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma flat_row_9 (i : Fin 16) :
    localFlat localTransfer 9 i = computedFlat 9 i := by
  fin_cases i
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (1 : Matrix Bool Bool ℂ)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      pauliX) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      pauliY) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      pauliZ) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliX)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliY)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliZ)) pauliY).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliY+pauliZ)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliZ+pauliX)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliX+pauliY)) pauliY).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliX)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliY)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliZ)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliY+Complex.I • pauliZ)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliZ+Complex.I • pauliX)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliX+Complex.I • pauliY)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma flat_row_10 (i : Fin 16) :
    localFlat localTransfer 10 i = computedFlat 10 i := by
  fin_cases i
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (1 : Matrix Bool Bool ℂ)) pauliY).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      pauliX) pauliY).trace.re = ((-1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      pauliY) pauliY).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      pauliZ) pauliY).trace.re = ((-1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliX)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliY)) pauliY).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliZ)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliY+pauliZ)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliZ+pauliX)) pauliY).trace.re = ((-1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliX+pauliY)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliX)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliY)) pauliY).trace.re = ((1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliZ)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliY+Complex.I • pauliZ)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliZ+Complex.I • pauliX)) pauliY).trace.re = ((-1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliX+Complex.I • pauliY)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma flat_row_11 (i : Fin 16) :
    localFlat localTransfer 11 i = computedFlat 11 i := by
  fin_cases i
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (1 : Matrix Bool Bool ℂ)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      pauliX) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      pauliY) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      pauliZ) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliX)) pauliY).trace.re = ((-1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliY)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliZ)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliY+pauliZ)) pauliY).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliZ+pauliX)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliX+pauliY)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliX)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliY)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliZ)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliY+Complex.I • pauliZ)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliZ+Complex.I • pauliX)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliX+Complex.I • pauliY)) pauliY).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma flat_row_12 (i : Fin 16) :
    localFlat localTransfer 12 i = computedFlat 12 i := by
  fin_cases i
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (1 : Matrix Bool Bool ℂ)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      pauliX) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      pauliY) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      pauliZ) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliX)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliY)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliZ)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliY+pauliZ)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliZ+pauliX)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliX+pauliY)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliX)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliY)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliZ)) pauliZ).trace.re = ((1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliY+Complex.I • pauliZ)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliZ+Complex.I • pauliX)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * ((1 : Matrix Bool Bool ℂ) * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliX+Complex.I • pauliY)) pauliZ).trace.re = ((-1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma flat_row_13 (i : Fin 16) :
    localFlat localTransfer 13 i = computedFlat 13 i := by
  fin_cases i
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (1 : Matrix Bool Bool ℂ)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      pauliX) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      pauliY) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      pauliZ) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliX)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliY)) pauliZ).trace.re = ((-1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliZ)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliY+pauliZ)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliZ+pauliX)) pauliZ).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliX+pauliY)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliX)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliY)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliZ)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliY+Complex.I • pauliZ)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliZ+Complex.I • pauliX)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliX * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliX+Complex.I • pauliY)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma flat_row_14 (i : Fin 16) :
    localFlat localTransfer 14 i = computedFlat 14 i := by
  fin_cases i
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (1 : Matrix Bool Bool ℂ)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      pauliX) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      pauliY) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      pauliZ) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliX)) pauliZ).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliY)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliZ)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliY+pauliZ)) pauliZ).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliZ+pauliX)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliX+pauliY)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliX)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliY)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliZ)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliY+Complex.I • pauliZ)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliZ+Complex.I • pauliX)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliY * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliX+Complex.I • pauliY)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma flat_row_15 (i : Fin 16) :
    localFlat localTransfer 15 i = computedFlat 15 i := by
  fin_cases i
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (1 : Matrix Bool Bool ℂ)) pauliZ).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      pauliX) pauliZ).trace.re = ((-1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      pauliY) pauliZ).trace.re = ((-1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      pauliZ) pauliZ).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliX)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliY)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • pauliZ)) pauliZ).trace.re = ((1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliY+pauliZ)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliZ+pauliX)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliX+pauliY)) pauliZ).trace.re = ((-1 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliX)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliY)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (1+pauliZ)) pauliZ).trace.re = ((1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliY+Complex.I • pauliZ)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliZ+Complex.I • pauliX)) pauliZ).trace.re = ((0 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · change (2⁻¹ : ℝ) * (pauliZ * krausApply (fun _ : Fin 1 =>
      (2⁻¹ : ℂ) • (pauliX+Complex.I • pauliY)) pauliZ).trace.re = ((-1/2 : ℚ) : ℝ)
    norm_num only [pauliX, pauliY, pauliZ, krausApply, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      Matrix.diag_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_inv, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, sqrt_mul_two, zero_div, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, sub_self, neg_zero, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma flat_value : localFlat localTransfer = computedFlat := by
  ext p i
  fin_cases p
  · exact flat_row_0 i
  · exact flat_row_1 i
  · exact flat_row_2 i
  · exact flat_row_3 i
  · exact flat_row_4 i
  · exact flat_row_5 i
  · exact flat_row_6 i
  · exact flat_row_7 i
  · exact flat_row_8 i
  · exact flat_row_9 i
  · exact flat_row_10 i
  · exact flat_row_11 i
  · exact flat_row_12 i
  · exact flat_row_13 i
  · exact flat_row_14 i
  · exact flat_row_15 i

private lemma flat_unit : IsUnit (localFlat localTransfer) := by
  rw [flat_value]
  exact isUnit_iff_exists_inv.mpr ⟨computedInverse, computed_inverse⟩

private lemma tensor_unit {n : ℕ}
    (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (complete : ∀ j, IsUnit (localFlat (B j))) : IsUnit (tensorFlat B) := by
  classical
  let C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℝ :=
    Matrix.of fun p i => ∏ j, (localFlat (B j))⁻¹ (p j) (i j)
  apply isUnit_iff_exists_inv.mpr
  refine ⟨C, ?_⟩
  ext p q
  change (∑ i : Fin n → Fin 16, (∏ j, localFlat (B j) (p j) (i j)) *
    ∏ j, (localFlat (B j))⁻¹ (i j) (q j)) = (1 : Matrix _ _ ℝ) p q
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (j : Fin n) (i : Fin 16) =>
    localFlat (B j) (p j) i * (localFlat (B j))⁻¹ i (q j))]
  have hlocal (j : Fin n) :
      (∑ i, localFlat (B j) (p j) i * (localFlat (B j))⁻¹ i (q j)) =
        (1 : Matrix (Fin 16) (Fin 16) ℝ) (p j) (q j) := by
    exact congrArg (fun A : Matrix (Fin 16) (Fin 16) ℝ => A (p j) (q j))
      (Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (complete j)))
  simp_rw [hlocal]
  by_cases h : p = q
  · subst q
    simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    rw [Matrix.one_apply_ne h]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact Matrix.one_apply_ne hj

private lemma interleave_injective {n : ℕ} :
    Function.Injective (interleave (n := n)) := by
  intro E F h
  ext a b
  let p : Fin n → Fin 16 := fun j => finProdFinEquiv (b j, a j)
  have he := congrFun h p
  simpa [interleave, p] using he

private lemma interleave_synthesis {n : ℕ}
    (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (q : (Fin n → Fin 16) → ℝ) :
    interleave (∑ i, q i • tensorOperation B i) = (tensorFlat B).mulVec q := by
  ext p
  simp only [interleave, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    tensorOperation, tensorFlat, localFlat, localBasisMatrix, Matrix.of_apply,
    Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

private lemma tensor_coordinates {n : ℕ}
    (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (complete : ∀ j, IsUnit (localFlat (B j)))
    (E : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ) :
    IsUnit (tensorFlat B) ∧
    E = ∑ i, tensorCoordinates B E i • tensorOperation B i ∧
    ∀ q, E = ∑ i, q i • tensorOperation B i → q = tensorCoordinates B E := by
  classical
  have hu := tensor_unit B complete
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hu
  refine ⟨hu, ?_, ?_⟩
  · apply interleave_injective
    rw [interleave_synthesis]
    simp [tensorCoordinates, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd]
  · intro q hq
    have hv := congrArg interleave hq
    rw [interleave_synthesis] at hv
    unfold tensorCoordinates
    rw [hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]

theorem solution :
    IsUnit (localFlat localTransfer) ∧
    ∀ n : ℕ, ∀ E : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ,
      ∃! q : (Fin n → Fin 16) → ℝ,
        E = ∑ i, q i • tensorOperation (fun _ => localTransfer) i := by
  refine ⟨flat_unit, ?_⟩
  intro n E
  obtain ⟨_, hs, hu⟩ := tensor_coordinates (fun _ : Fin n => localTransfer)
    (fun _ => flat_unit) E
  exact ⟨_, hs, hu⟩

#print axioms solution
