-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P10.gateFidelity_pauli
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:25:37.807852+00:00
-- url     : https://prove2.me/submissions/93353504-837e-4b21-a38a-3fa9a3165d79

import Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P10_gateFidelity_operatorBasis

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P10

private def fourPaulis : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![1, pauliOperators 0, pauliOperators 1, pauliOperators 2]

private lemma fourPaulis_star (j : Fin 4) : star (fourPaulis j) = fourPaulis j := by
  fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [fourPaulis, pauliOperators, pauliX, pauliY, pauliZ, finTwoEquiv,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Matrix.diagonal_apply]

private lemma fourPaulis_orthogonal (j k : Fin 4) :
    (star (fourPaulis j) * fourPaulis k).trace = if j = k then (2 : ℂ) else 0 := by
  fin_cases j <;> fin_cases k <;>
    norm_num [fourPaulis, pauliOperators, pauliX, pauliY, pauliZ, finTwoEquiv,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.one_apply,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Matrix.diagonal_apply]

private lemma fourPaulis_unitary (j : Fin 4) :
    fourPaulis j ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [fourPaulis, pauliOperators, pauliX, pauliY, pauliZ, finTwoEquiv,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.one_apply,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Matrix.diagonal_apply]

private lemma fourPaulis_independent : LinearIndependent ℂ fourPaulis := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  have h := congrArg (fun X => (star (fourPaulis i) * X).trace) hg
  have hzero : (2 : ℂ) * g i = 0 := by
    simpa only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
      smul_eq_mul, fourPaulis_orthogonal, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Matrix.mul_zero, Matrix.trace_zero, mul_comm] using h
  exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)

private def pauliBasis : OrthogonalUnitaryOperatorBasis 2 where
  basis := basisOfLinearIndependentOfCardEqFinrank fourPaulis_independent
    (by norm_num [Module.finrank_matrix])
  unitary := by
    simpa only [coe_basisOfLinearIndependentOfCardEqFinrank] using fourPaulis_unitary
  orthogonal := by
    simpa only [coe_basisOfLinearIndependentOfCardEqFinrank, Nat.cast_ofNat] using fourPaulis_orthogonal

private lemma pauliBasis_apply (j : Fin 4) : pauliBasis.basis j = fourPaulis j := by
  simp [pauliBasis]

private lemma channel_trace {d : ℕ} (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (X : Matrix (Fin d) (Fin d) ℂ) : (E X).trace = X.trace := by
  obtain ⟨m, K, hK, hE⟩ := hE
  calc
    (E X).trace = ∑ j, ((K j)ᴴ * K j * X).trace := by
      rw [hE]
      simp only [krausApply, Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact Matrix.trace_mul_cycle _ _ _
    _ = ((∑ j, (K j)ᴴ * K j) * X).trace := by
      rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = X.trace := by rw [hK, Matrix.one_mul]

/-- Nielsen Eq. (18): use the I,X,Y,Z basis and trace preservation. -/
theorem solution (E : Superop (Fin 2) (Fin 2)) (hE : IsChannel E)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    gateFidelity 2 (by omega) E U = 1/2+(1/12 : ℝ)*
      ∑ j : Fin 3, ((U : Matrix (Fin 2) (Fin 2) ℂ)*pauliOperators j*
        star (U : Matrix (Fin 2) (Fin 2) ℂ)*E (pauliOperators j)).trace.re := by
  rw [gateFidelity_operatorBasis 2 (by omega) E hE U pauliBasis]
  simp_rw [pauliBasis_apply, fourPaulis_star]
  have hidentity : ((U : Matrix (Fin 2) (Fin 2) ℂ) * fourPaulis 0 *
      star (U : Matrix (Fin 2) (Fin 2) ℂ) * E (fourPaulis 0)).trace.re = 2 := by
    simp only [fourPaulis, Matrix.cons_val_zero, Matrix.mul_one, (Matrix.mem_unitaryGroup_iff.mp U.property),
      Matrix.one_mul, channel_trace E hE]
    norm_num [Matrix.trace, Fin.sum_univ_two]
  rw [Fin.sum_univ_succ, hidentity]
  have hp (j : Fin 3) : fourPaulis j.succ = pauliOperators j := by
    fin_cases j <;> rfl
  simp_rw [hp]
  norm_num
  ring
