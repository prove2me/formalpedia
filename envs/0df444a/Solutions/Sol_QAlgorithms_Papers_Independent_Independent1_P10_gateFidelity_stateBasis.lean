-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P10.gateFidelity_stateBasis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:26:09.005855+00:00
-- url     : https://prove2.me/submissions/cc1b1483-c366-422c-9a61-4b8a5dd651f8

import Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P10_gateFidelity_operatorBasis

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P10

private lemma channel_linear {d : ℕ} (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) :
    ∃ L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ, ∀ X, L X = E X := by
  obtain ⟨m, K, _, hK⟩ := hE
  refine ⟨{ toFun := E, map_add' := ?_, map_smul' := ?_ }, fun _ => rfl⟩
  · intro X Y
    simp only [hK, krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  · intro c X
    simp only [hK, krausApply, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum]
    rfl

/-- Nielsen Eq. (19): expand each unitary basis vector in the state operator basis. -/
theorem solution (d : ℕ) (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (B : OrthogonalUnitaryOperatorBasis d)
    (R : StateOperatorBasis d) :
    gateFidelity d hd E U =
      ((∑ j, ∑ k, ((R.basis.repr (B.basis j) k)*
        ((U : Matrix (Fin d) (Fin d) ℂ)*star (B.basis j)*
          star (U : Matrix (Fin d) (Fin d) ℂ)*E (R.basis k)).trace).re)+(d : ℝ)^2) /
            ((d : ℝ)^2*((d : ℝ)+1)) := by
  rw [gateFidelity_operatorBasis d hd E hE U B]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  obtain ⟨L, hL⟩ := channel_linear E hE
  have hX : E (B.basis j) = ∑ k, R.basis.repr (B.basis j) k • E (R.basis k) := by
    simp_rw [← hL]
    have h := congrArg L (R.basis.sum_repr (B.basis j))
    simpa only [map_sum, map_smul] using h.symm
  rw [hX]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, Complex.re_sum]
