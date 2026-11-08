-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P88.operator_width_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:32:42.884921+00:00
-- url     : https://prove2.me/submissions/79ccadc6-4465-475c-81b2-e3a831681b21

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

open QAlgorithms.Papers.Independent.Intakenext100.P88 in
theorem solution (h : ℕ) (hh : 0 < h)
    (S : Submodule ℝ (Matrix (Fin h) (Fin h) ℂ))
    (hS : ∀ A ∈ S, A.IsHermitian) :
    Module.finrank ℝ S ≤ h ^ 2 := by
  let f : S →ₗ[ℝ] Matrix (Fin h) (Fin h) ℝ :=
    { toFun := fun A => Matrix.of fun i j =>
        ((A : Matrix (Fin h) (Fin h) ℂ) i j).re + ((A : Matrix (Fin h) (Fin h) ℂ) i j).im
      map_add' := by
        intro A B; ext i j; simp; ring
      map_smul' := by
        intro c A; ext i j; simp; ring }
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro A hA
    have hH := hS A A.2
    apply Subtype.ext
    ext i j
    have e1 : (f A) i j = 0 := by rw [hA]; rfl
    have e2 : (f A) j i = 0 := by rw [hA]; rfl
    change ((A : Matrix (Fin h) (Fin h) ℂ) i j).re +
      ((A : Matrix (Fin h) (Fin h) ℂ) i j).im = 0 at e1
    change ((A : Matrix (Fin h) (Fin h) ℂ) j i).re +
      ((A : Matrix (Fin h) (Fin h) ℂ) j i).im = 0 at e2
    have hji := hH.apply i j
    have r1 := congrArg Complex.re hji
    have r2 := congrArg Complex.im hji
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at r1 r2
    simp only [Submodule.coe_zero, Matrix.zero_apply]
    apply Complex.ext
    · simp only [Complex.zero_re]; linarith
    · simp only [Complex.zero_im]; linarith
  calc Module.finrank ℝ S ≤ Module.finrank ℝ (Matrix (Fin h) (Fin h) ℝ) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = h ^ 2 := by simp [Module.finrank_matrix, sq]
