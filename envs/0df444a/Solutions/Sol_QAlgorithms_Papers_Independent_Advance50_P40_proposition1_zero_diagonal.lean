-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P40.proposition1_zero_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:16:12.963992+00:00
-- url     : https://prove2.me/submissions/3f1f040d-208a-4137-b1e2-597464066b08

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P40
noncomputable section

open QAlgorithms.Papers.Independent.Advance50.P40
open scoped ComplexOrder

theorem solution {n m : ℕ} [NeZero n] [NeZero m]
    (phi : BathFamily n m) (hphi : IsSLFamily phi)
    (R : SystemMatrix n) (hR : IsSLAdmissibleInput phi R) (hcp : AllUnitaryCP phi)
    (k l : Fin n) (hkl : k ≠ l) (hzero : phi k k = 0 ∨ phi l l = 0) :
    phi k l = 0 ∧ phi l k = 0 := by
  obtain ⟨F, hF, hCP⟩ := hcp 1
  have hred : ∀ (M : SystemMatrix n) i j, F M i j = M i j * Matrix.trace (phi i j) := by
    intro M i j
    rw [hF]
    simp [specifiedReducedMap, qdp, QAlgorithms.traceRight, sourceAssignment, Matrix.trace,
      Finset.mul_sum]
  let v : Fin n × Fin n → ℂ := fun p => if p.1 = p.2 then 1 else 0
  have hX : (Matrix.vecMulVec v (star v)).PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  have hY := hCP n _ hX
  let e : Fin 2 → Fin n × Fin n := ![(k, k), (l, l)]
  have hS := (hY.submatrix e).det_nonneg
  have hT : Matrix.trace (phi l k) = star (Matrix.trace (phi k l)) := by
    rw [hphi.2 k l, Matrix.trace_conjTranspose]
  have hkk : Matrix.trace (phi k k) * Matrix.trace (phi l l) = 0 := by
    rcases hzero with h | h <;> simp [h]
  have hYe : ∀ a b : Fin n, QAlgorithms.idTensorSuperop (⇑F) (Matrix.vecMulVec v (star v))
      (a, a) (b, b) = Matrix.trace (phi a b) := by
    intro a b
    simp [QAlgorithms.idTensorSuperop, hred, v, Matrix.vecMulVec]
  rw [Matrix.det_fin_two] at hS
  simp only [e, Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, hYe] at hS
  rw [hT] at hS
  have h0 : Matrix.trace (phi k l) = 0 := by
    have : (0 : ℂ) ≤ -(Complex.normSq (Matrix.trace (phi k l)) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
      convert hS using 1
      have := hkk
      simp only [Complex.star_def] at *
      linear_combination -this
    have h2 : Complex.normSq (Matrix.trace (phi k l)) ≤ 0 := by
      have := (Complex.nonneg_iff.mp this).1
      simpa using this
    exact Complex.normSq_eq_zero.mp (le_antisymm h2 (Complex.normSq_nonneg _))
  have hkl0 : phi k l = 0 := by
    rcases hphi.1 k l with h | h
    · exact h
    · rw [h] at h0; exact absurd h0 one_ne_zero
  refine ⟨hkl0, ?_⟩
  rw [hphi.2 k l, hkl0, Matrix.conjTranspose_zero]
