-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P09.tableSynthesis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:21:32.909694+00:00
-- url     : https://prove2.me/submissions/56b62809-2e72-4cc3-abc0-600561e376e4

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
noncomputable section
open scoped Matrix ComplexOrder NNReal ENNReal
open QAlgorithms QAlgorithms.ErrorMitigation QAlgorithms.Papers.Independent.Independent1.P09

private def m2 (a b c d : ℂ) : Matrix Bool Bool ℂ :=
  Matrix.of fun i j => if i then (if j then d else c) else (if j then b else a)

private def rx : Matrix Bool Bool ℂ :=
  m2 (1/2+(-1/2)*Complex.I) (1/2+(1/2)*Complex.I)
    (1/2+(1/2)*Complex.I) (1/2+(-1/2)*Complex.I)
private def rz : Matrix Bool Bool ℂ := m2 (1) (0) (0) (0+(-1)*Complex.I)
private def pi0 : Matrix Bool Bool ℂ := m2 1 0 0 0

private lemma rz_word :
    ([TableLetter.s, .s, .s].map TableLetter.mat).prod = rz := by
  ext i j
  cases i <;> cases j <;>
    norm_num [TableLetter.mat, phaseS, rz, m2, Matrix.mul_apply, Fintype.sum_bool,
      Matrix.diagonal_apply]

private lemma rx_word :
    ([TableLetter.h, .s, .s, .s, .h].map TableLetter.mat).prod = rx := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  ext i j
  cases i <;> cases j <;>
    apply Complex.ext <;>
    norm_num [TableLetter.mat, hadamard, phaseS, rx, m2, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.diagonal_apply] <;>
    field_simp <;> nlinarith

private lemma pi_word : ([TableLetter.project].map TableLetter.mat).prod = pi0 := by
  ext i j
  cases i <;> cases j <;>
    norm_num [TableLetter.mat, pi0, m2, Matrix.single_apply]

private def compact (i : Fin 16) : Matrix Bool Bool ℂ :=
  ![1,rx*rx,rx*rx*rz*rz,rz*rz,rx,rz*rz*rz*rx*rz,rz,
    rx*rz*rz,rz*rx*rz,rx*rx*rz,
    rz*rz*rz*rx*rx*rx*pi0*rx*rz,
    rx*pi0*rx*rx*rx,pi0,
    rz*rz*rz*rx*rx*rx*pi0*rx*rx*rx*rz,
    rx*pi0*rx*rx*rx*rz*rz,pi0*rx*rx] i

private lemma word_compact (i : Fin 16) :
    ((tableWord i).map TableLetter.mat).prod = compact i := by
  fin_cases i <;>
    simp only [tableWord, compact, Matrix.cons_val_zero', Matrix.cons_val_succ',
      List.map_append, List.prod_append, rx_word, rz_word, pi_word, List.map_nil,
      List.prod_nil]




private def evaluated (i : Fin 16) : Matrix Bool Bool ℂ :=
  ![m2 (1) (0) (0) (1),
    m2 (0) (1) (1) (0),
    m2 (0) (-1) (1) (0),
    m2 (1) (0) (0) (-1),
    m2 (1/2+(-1/2)*Complex.I) (1/2+(1/2)*Complex.I) (1/2+(1/2)*Complex.I) (1/2+(-1/2)*Complex.I),
    m2 (1/2+(-1/2)*Complex.I) (1/2+(-1/2)*Complex.I) (-1/2+(1/2)*Complex.I) (1/2+(-1/2)*Complex.I),
    m2 (1) (0) (0) (0+(-1)*Complex.I),
    m2 (1/2+(-1/2)*Complex.I) (-1/2+(-1/2)*Complex.I) (1/2+(1/2)*Complex.I) (-1/2+(1/2)*Complex.I),
    m2 (1/2+(-1/2)*Complex.I) (1/2+(-1/2)*Complex.I) (1/2+(-1/2)*Complex.I) (-1/2+(1/2)*Complex.I),
    m2 (0) (0+(-1)*Complex.I) (1) (0),
    m2 (1/2) (1/2) (1/2) (1/2),
    m2 (1/2) (0+(-1/2)*Complex.I) (0+(1/2)*Complex.I) (1/2),
    m2 (1) (0) (0) (0),
    m2 (0+(1/2)*Complex.I) (0+(-1/2)*Complex.I) (0+(1/2)*Complex.I) (0+(-1/2)*Complex.I),
    m2 (1/2) (0+(1/2)*Complex.I) (0+(1/2)*Complex.I) (-1/2),
    m2 (0) (1) (0) (0)] i


private lemma mul_step_0 : rx * rx =
    m2 (0) (1) (1) (0) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_1 : m2 (0) (1) (1) (0) * rz =
    m2 (0) (0+(-1)*Complex.I) (1) (0) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_2 : m2 (0) (0+(-1)*Complex.I) (1) (0) * rz =
    m2 (0) (-1) (1) (0) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_3 : rz * rz =
    m2 (1) (0) (0) (-1) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_4 : m2 (1) (0) (0) (-1) * rz =
    m2 (1) (0) (0) (0+(1)*Complex.I) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_5 : m2 (1) (0) (0) (0+(1)*Complex.I) * rx =
    m2 (1/2+(-1/2)*Complex.I) (1/2+(1/2)*Complex.I) (-1/2+(1/2)*Complex.I) (1/2+(1/2)*Complex.I) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_6 : m2 (1/2+(-1/2)*Complex.I) (1/2+(1/2)*Complex.I) (-1/2+(1/2)*Complex.I) (1/2+(1/2)*Complex.I) * rz =
    m2 (1/2+(-1/2)*Complex.I) (1/2+(-1/2)*Complex.I) (-1/2+(1/2)*Complex.I) (1/2+(-1/2)*Complex.I) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_7 : rx * rz =
    m2 (1/2+(-1/2)*Complex.I) (1/2+(-1/2)*Complex.I) (1/2+(1/2)*Complex.I) (-1/2+(-1/2)*Complex.I) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_8 : m2 (1/2+(-1/2)*Complex.I) (1/2+(-1/2)*Complex.I) (1/2+(1/2)*Complex.I) (-1/2+(-1/2)*Complex.I) * rz =
    m2 (1/2+(-1/2)*Complex.I) (-1/2+(-1/2)*Complex.I) (1/2+(1/2)*Complex.I) (-1/2+(1/2)*Complex.I) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_9 : rz * rx =
    m2 (1/2+(-1/2)*Complex.I) (1/2+(1/2)*Complex.I) (1/2+(-1/2)*Complex.I) (-1/2+(-1/2)*Complex.I) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_10 : m2 (1/2+(-1/2)*Complex.I) (1/2+(1/2)*Complex.I) (1/2+(-1/2)*Complex.I) (-1/2+(-1/2)*Complex.I) * rz =
    m2 (1/2+(-1/2)*Complex.I) (1/2+(-1/2)*Complex.I) (1/2+(-1/2)*Complex.I) (-1/2+(1/2)*Complex.I) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_11 : m2 (1/2+(-1/2)*Complex.I) (1/2+(1/2)*Complex.I) (-1/2+(1/2)*Complex.I) (1/2+(1/2)*Complex.I) * rx =
    m2 (0) (1) (0+(1)*Complex.I) (0) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_12 : m2 (0) (1) (0+(1)*Complex.I) (0) * rx =
    m2 (1/2+(1/2)*Complex.I) (1/2+(-1/2)*Complex.I) (1/2+(1/2)*Complex.I) (-1/2+(1/2)*Complex.I) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_13 : m2 (1/2+(1/2)*Complex.I) (1/2+(-1/2)*Complex.I) (1/2+(1/2)*Complex.I) (-1/2+(1/2)*Complex.I) * pi0 =
    m2 (1/2+(1/2)*Complex.I) (0) (1/2+(1/2)*Complex.I) (0) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_14 : m2 (1/2+(1/2)*Complex.I) (0) (1/2+(1/2)*Complex.I) (0) * rx =
    m2 (1/2) (0+(1/2)*Complex.I) (1/2) (0+(1/2)*Complex.I) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_15 : m2 (1/2) (0+(1/2)*Complex.I) (1/2) (0+(1/2)*Complex.I) * rz =
    m2 (1/2) (1/2) (1/2) (1/2) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_16 : rx * pi0 =
    m2 (1/2+(-1/2)*Complex.I) (0) (1/2+(1/2)*Complex.I) (0) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_17 : m2 (1/2+(-1/2)*Complex.I) (0) (1/2+(1/2)*Complex.I) (0) * rx =
    m2 (0+(-1/2)*Complex.I) (1/2) (1/2) (0+(1/2)*Complex.I) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_18 : m2 (0+(-1/2)*Complex.I) (1/2) (1/2) (0+(1/2)*Complex.I) * rx =
    m2 (0) (1/2+(-1/2)*Complex.I) (0) (1/2+(1/2)*Complex.I) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_19 : m2 (0) (1/2+(-1/2)*Complex.I) (0) (1/2+(1/2)*Complex.I) * rx =
    m2 (1/2) (0+(-1/2)*Complex.I) (0+(1/2)*Complex.I) (1/2) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_20 : m2 (1/2) (0+(1/2)*Complex.I) (1/2) (0+(1/2)*Complex.I) * rx =
    m2 (0) (1/2+(1/2)*Complex.I) (0) (1/2+(1/2)*Complex.I) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_21 : m2 (0) (1/2+(1/2)*Complex.I) (0) (1/2+(1/2)*Complex.I) * rx =
    m2 (0+(1/2)*Complex.I) (1/2) (0+(1/2)*Complex.I) (1/2) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_22 : m2 (0+(1/2)*Complex.I) (1/2) (0+(1/2)*Complex.I) (1/2) * rz =
    m2 (0+(1/2)*Complex.I) (0+(-1/2)*Complex.I) (0+(1/2)*Complex.I) (0+(-1/2)*Complex.I) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_23 : m2 (1/2) (0+(-1/2)*Complex.I) (0+(1/2)*Complex.I) (1/2) * rz =
    m2 (1/2) (-1/2) (0+(1/2)*Complex.I) (0+(-1/2)*Complex.I) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_24 : m2 (1/2) (-1/2) (0+(1/2)*Complex.I) (0+(-1/2)*Complex.I) * rz =
    m2 (1/2) (0+(1/2)*Complex.I) (0+(1/2)*Complex.I) (-1/2) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_25 : pi0 * rx =
    m2 (1/2+(-1/2)*Complex.I) (1/2+(1/2)*Complex.I) (0) (0) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma mul_step_26 : m2 (1/2+(-1/2)*Complex.I) (1/2+(1/2)*Complex.I) (0) (0) * rx =
    m2 (0) (1) (0) (0) := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;>
    norm_num [rx, rz, pi0, m2, Matrix.mul_apply, Fintype.sum_bool]

private lemma compact_evaluated (i : Fin 16) : compact i = evaluated i := by
  fin_cases i <;>
    simp only [compact, evaluated, Matrix.cons_val_zero', Matrix.cons_val_succ',
      mul_step_0, mul_step_1, mul_step_2, mul_step_3, mul_step_4, mul_step_5, mul_step_6, mul_step_7, mul_step_8, mul_step_9, mul_step_10, mul_step_11, mul_step_12, mul_step_13, mul_step_14, mul_step_15, mul_step_16, mul_step_17, mul_step_18, mul_step_19, mul_step_20, mul_step_21, mul_step_22, mul_step_23, mul_step_24, mul_step_25, mul_step_26] <;>
    first | rfl | (ext a b; cases a <;> cases b <;> rfl)

private def phase (i : Fin 16) : ℂ :=
  ![(1),
    (1),
    (0+(-1)*Complex.I),
    (1),
    (1+(-1)*Complex.I)*((Real.sqrt 2)⁻¹ : ℂ),
    (1+(-1)*Complex.I)*((Real.sqrt 2)⁻¹ : ℂ),
    (1+(-1)*Complex.I)*((Real.sqrt 2)⁻¹ : ℂ),
    (1+(-1)*Complex.I)*((Real.sqrt 2)⁻¹ : ℂ),
    (1+(-1)*Complex.I)*((Real.sqrt 2)⁻¹ : ℂ),
    (1+(-1)*Complex.I)*((Real.sqrt 2)⁻¹ : ℂ),
    (1),
    (1),
    (1),
    (1),
    (1),
    (1)] i

private lemma evaluated_phase (i : Fin 16) : evaluated i = phase i • tableIMatrix i := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  fin_cases i <;> ext a b <;> cases a <;> cases b <;>
    apply Complex.ext <;>
    norm_num [evaluated, phase, tableIMatrix, pauliX, pauliY, pauliZ, m2,
      Matrix.diagonal_apply, Matrix.one_apply] <;>
    field_simp <;> nlinarith

private lemma phase_unit (i : Fin 16) : star (phase i) * phase i = 1 := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  fin_cases i <;> apply Complex.ext <;>
    norm_num [phase, Complex.star_def] <;> field_simp <;> nlinarith

theorem solution : ∀ i : Fin 16, tableWordMap i = tableIBasis i := by
  intro i
  apply LinearMap.ext
  intro X
  change krausApply (fun _ : Fin 1 => ((tableWord i).map TableLetter.mat).prod) X =
    krausApply (fun _ : Fin 1 => tableIMatrix i) X
  simp only [krausApply, Fin.sum_univ_one, word_compact, compact_evaluated, evaluated_phase,
    Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    phase_unit, one_smul]

#print axioms solution
