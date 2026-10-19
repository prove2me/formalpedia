-- Prove2me | solution 1 for QAlgorithms.Nannicini.pauli_basis_hermitian_xyz
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-17T21:23:08.428577+00:00
-- url     : https://prove2.me/submissions/73d29d97-5fa4-4a8e-9494-d3ecda95ebd6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates

set_option autoImplicit false
open QAlgorithms

private theorem pauli_li :
    LinearIndependent ℂ ![(1 : Matrix Bool Bool ℂ), pauliX, pauliY, pauliZ] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h00 := congrFun (congrFun hg false) false
  have h01 := congrFun (congrFun hg false) true
  have h10 := congrFun (congrFun hg true) false
  have h11 := congrFun (congrFun hg true) true
  simp [Fin.sum_univ_four, pauliX, pauliY, pauliZ] at h00 h01 h10 h11
  have e0 : g 0 = 0 := by linear_combination (1 / 2 : ℂ) * h00 + (1 / 2 : ℂ) * h11
  have e3 : g 3 = 0 := by linear_combination (1 / 2 : ℂ) * h00 - (1 / 2 : ℂ) * h11
  have e1 : g 1 = 0 := by linear_combination (1 / 2 : ℂ) * h01 + (1 / 2 : ℂ) * h10
  have e2 : g 2 = 0 := by
    have : Complex.I * g 2 = 0 := by linear_combination (1 / 2 : ℂ) * h10 - (1 / 2 : ℂ) * h01
    simpa [Complex.I_ne_zero] using this
  intro i
  fin_cases i <;> simpa

theorem solution :
    LinearIndependent ℂ ![(1 : Matrix Bool Bool ℂ), pauliX, pauliY, pauliZ] ∧
    Submodule.span ℂ (Set.range ![(1 : Matrix Bool Bool ℂ), pauliX, pauliY, pauliZ]) = ⊤ ∧
    (1 : Matrix Bool Bool ℂ).IsHermitian ∧ pauliX.IsHermitian ∧ pauliY.IsHermitian ∧
    pauliZ.IsHermitian ∧
    pauliX * pauliY * pauliZ = Complex.I • (1 : Matrix Bool Bool ℂ) := by
  refine ⟨pauli_li, ?_, Matrix.isHermitian_one, ?_, ?_, ?_, ?_⟩
  · apply pauli_li.span_eq_top_of_card_eq_finrank'
    simp [Module.finrank_matrix]
  · ext a b; cases a <;> cases b <;> simp [pauliX, Matrix.conjTranspose_apply]
  · ext a b; cases a <;> cases b <;> simp [pauliY, Matrix.conjTranspose_apply]
  · ext a b; cases a <;> cases b <;> simp [pauliZ, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  · ext a b
    cases a <;> cases b <;>
      simp [Matrix.mul_apply, Fintype.sum_bool, pauliX, pauliY, pauliZ, Matrix.diagonal_apply]
