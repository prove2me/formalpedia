-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P52.pauli_propagation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T01:26:52.998074+00:00
-- url     : https://prove2.me/submissions/98f6c972-9915-41a6-ac33-bbe72677f073

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

open QAlgorithms QAlgorithms.Papers.Independent.Intakenext100.P52 in
theorem solution (theta : ℝ) :
    rx theta * pauliX = pauliX * rx theta ∧
    rx theta * pauliZ = pauliZ * rx (-theta) ∧
    rz theta * pauliX = pauliX * rz (-theta) ∧
    rz theta * pauliZ = pauliZ * rz theta ∧
    wGate theta * pauliZ = pauliX * wGate theta ∧
    wGate theta * pauliX = Complex.exp (Complex.I * theta) • (pauliZ * wGate (-theta)) ∧
    controlled pauliZ * Matrix.kronecker pauliZ 1 = Matrix.kronecker pauliZ 1 * controlled pauliZ ∧
    controlled pauliZ * Matrix.kronecker pauliX 1 = Matrix.kronecker pauliX pauliZ * controlled pauliZ ∧
    controlled pauliZ * Matrix.kronecker 1 pauliZ = Matrix.kronecker 1 pauliZ * controlled pauliZ ∧
    controlled pauliZ * Matrix.kronecker 1 pauliX = Matrix.kronecker pauliZ pauliX * controlled pauliZ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext a b
    cases a <;> cases b <;>
      simp [rx, pauliX, Matrix.mul_apply, Fintype.sum_bool, Matrix.one_apply]
  · ext a b
    cases a <;> cases b <;>
      simp [rx, pauliX, pauliZ, Matrix.mul_apply, Fintype.sum_bool, Matrix.one_apply,
        Matrix.diagonal_apply] <;> ring
  · ext a b
    cases a <;> cases b <;>
      simp [rz, pauliX, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply]
  · ext a b
    cases a <;> cases b <;>
      simp [rz, pauliZ, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply]
  · ext a b
    cases a <;> cases b <;>
      simp [wGate, phaseGate, hadamard, pauliX, pauliZ, Matrix.mul_apply, Fintype.sum_bool,
        Matrix.diagonal_apply]
  · have hP1 : phaseGate theta =
        Matrix.diagonal (fun b => if b then Complex.exp (Complex.I * theta) else 1) := rfl
    have hP2 : phaseGate (-theta) =
        Matrix.diagonal (fun b => if b then (Complex.exp (Complex.I * theta))⁻¹ else 1) := by
      unfold phaseGate
      congr 1
      funext b
      rw [Complex.ofReal_neg, mul_neg, Complex.exp_neg]
    have hu0 : Complex.exp (Complex.I * theta) ≠ 0 := Complex.exp_ne_zero _
    simp only [wGate, hP1, hP2]
    generalize Complex.exp (Complex.I * theta) = u at hu0 ⊢
    ext a b
    cases a <;> cases b <;>
      simp [hadamard, pauliX, pauliZ, Matrix.mul_apply, Fintype.sum_bool,
        Matrix.diagonal_apply, hu0] <;>
      (try field_simp) <;> (try ring_nf)
  · ext ⟨a1, a2⟩ ⟨b1, b2⟩
    cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;>
      simp [controlled, pauliZ, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool,
        Matrix.kronecker_apply, Matrix.one_apply, Matrix.diagonal_apply]
  · ext ⟨a1, a2⟩ ⟨b1, b2⟩
    cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;>
      simp [controlled, pauliZ, pauliX, Matrix.mul_apply, Fintype.sum_prod_type,
        Fintype.sum_bool, Matrix.kronecker_apply, Matrix.one_apply, Matrix.diagonal_apply]
  · ext ⟨a1, a2⟩ ⟨b1, b2⟩
    cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;>
      simp [controlled, pauliZ, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool,
        Matrix.kronecker_apply, Matrix.one_apply, Matrix.diagonal_apply]
  · ext ⟨a1, a2⟩ ⟨b1, b2⟩
    cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;>
      simp [controlled, pauliZ, pauliX, Matrix.mul_apply, Fintype.sum_prod_type,
        Fintype.sum_bool, Matrix.kronecker_apply, Matrix.one_apply, Matrix.diagonal_apply]

end
