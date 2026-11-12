-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P47.z2_example
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T02:24:27.67524+00:00
-- url     : https://prove2.me/submissions/8d52e2b6-12af-4019-b4d2-3cef350761d9

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P47

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P47 in
theorem solution :
    ((1 / 2 : ℂ) • ((1 : Mat Bool) + pauliZ)) = Matrix.single false false 1 ∧
    ∀ rho : Mat Bool, IsDensityMatrix rho →
      controlReturnProbability ((1 / 2 : ℂ) • ((1 : Mat Bool) + pauliZ)) rho = (rho false false).re ∧
      (Bose ((1 / 2 : ℂ) • ((1 : Mat Bool) + pauliZ)) rho ↔
        rho = Matrix.single false false 1) ∧
      (Sym (fun g : Bool => if g then pauliZ else 1) rho ↔
        ∀ i j, i ≠ j → rho i j = 0) := by
  have hQ : ((1 / 2 : ℂ) • ((1 : Mat Bool) + pauliZ)) = Matrix.single false false 1 := by
    ext i j
    cases i <;> cases j <;>
      simp [pauliZ, Matrix.single_apply, Matrix.one_apply, Matrix.diagonal_apply] <;> norm_num
  refine ⟨hQ, ?_⟩
  intro rho hrho
  rw [hQ]
  have htr : rho true true + rho false false = 1 := by
    have h := hrho.2
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_bool] at h
    exact h
  have hEρE : Matrix.single false false (1 : ℂ) * rho * Matrix.single false false 1 =
      Matrix.single false false (rho false false) := by
    rw [Matrix.single_mul_mul_single, one_mul, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · unfold controlReturnProbability effectProb
    rw [Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same, mul_one]
    simp [Matrix.trace, Fintype.sum_bool, Matrix.mul_apply, Matrix.single_apply]
  · constructor
    · rintro ⟨_, h⟩
      rw [hEρE] at h
      have htt : rho true true = 0 := by
        rw [h]; simp [Matrix.single_apply]
      have hff : rho false false = 1 := by
        rw [htt, zero_add] at htr; exact htr
      rw [h, hff]
    · intro h
      refine ⟨hrho, ?_⟩
      rw [hEρE, h]
      simp [Matrix.single_apply]
  · constructor
    · rintro ⟨_, h⟩ i j hij
      have hz := congrFun (congrFun (h true) i) j
      cases i <;> cases j
      · exact absurd rfl hij
      · simp [pauliZ, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply,
          Matrix.conjTranspose_apply] at hz ⊢
        first | exact hz | linear_combination hz / 2
      · simp [pauliZ, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply,
          Matrix.conjTranspose_apply] at hz ⊢
        first | exact hz | linear_combination hz / 2
      · exact absurd rfl hij
    · intro h
      refine ⟨hrho, fun g => ?_⟩
      cases g
      · simp
      · ext i j
        cases i <;> cases j <;>
          simp [pauliZ, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply,
            Matrix.conjTranspose_apply, h]

end
