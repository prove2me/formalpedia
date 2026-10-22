-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P18.real_input_perfect_not
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:24:40.101368+00:00
-- url     : https://prove2.me/submissions/650e7a91-13b9-4f4f-8c61-61c8fe14fe61

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P18
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support21.P18

open MeasureTheory Filter

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

lemma g71g1_real_unit (psi : EuclideanSpace ℂ (Fin 2)) (hpsi : IsState psi)
    (hr : HasRealCoordinates psi) :
    psi 0 = ((psi 0).re : ℂ) ∧ psi 1 = ((psi 1).re : ℂ) ∧ (psi 0).re ^ 2 + (psi 1).re ^ 2 = 1 := by
  have h0 : psi 0 = ((psi 0).re : ℂ) := Complex.ext (by simp) (by simp [hr 0])
  have h1 : psi 1 = ((psi 1).re : ℂ) := Complex.ext (by simp) (by simp [hr 1])
  refine ⟨h0, h1, ?_⟩
  unfold IsState at hpsi
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_two] at hpsi
  rw [h0, h1, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, sq_abs] at hpsi
  exact hpsi

theorem solution :
    realNotMatrix ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
    IsChannel (conjSuperop realNotMatrix) ∧
    ∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi → HasRealCoordinates psi →
      act realNotMatrix psi = theta psi ∧
      conjSuperop realNotMatrix (pureDensity psi) = orthogonalDensity psi ∧
      effectProb (orthogonalDensity psi) (conjSuperop realNotMatrix (pureDensity psi)) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [realNotMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  · refine ⟨1, fun _ => realNotMatrix, ?_, ?_⟩
    · unfold IsKrausFamily
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [realNotMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    · intro ρ; simp [krausApply, conjSuperop]
  · intro psi hpsi hr
    obtain ⟨h0, h1, hn⟩ := g71g1_real_unit psi hpsi hr
    set a := (psi 0).re
    set b := (psi 1).re
    have hnC : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast hn
    have hp : pureDensity psi = !![(a : ℂ) * a, a * b; b * a, b * b] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [pureDensity, h0, h1]
    have hconj : conjSuperop realNotMatrix (pureDensity psi) = orthogonalDensity psi := by
      rw [orthogonalDensity, hp]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [conjSuperop, realNotMatrix, Matrix.mul_apply,
          Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
        first | linear_combination hnC | linear_combination -hnC | ring
    refine ⟨?_, hconj, ?_⟩
    · ext i; fin_cases i <;>
        simp [act, theta, realNotMatrix, dotProduct, Fin.sum_univ_two, h0, h1]
    · rw [hconj, orthogonalDensity, hp]
      simp [effectProb, Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply]
      linear_combination (a ^ 2 + b ^ 2 - 1) * hn
