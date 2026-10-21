-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P09.qubit_explicit_completion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:11:12.715422+00:00
-- url     : https://prove2.me/submissions/296566fb-b083-4cac-9e01-a1382b97f56a

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09
noncomputable section
open QAlgorithms.Papers.Independent.Support21.P09
open scoped BigOperators ComplexConjugate

theorem g66c_sbZ : sumBlock pauliZFin pauliZFin = !![1,0,0,0; 0,-1,0,0; 0,0,1,0; 0,0,0,-1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sumBlock, pauliZFin, QAlgorithms.pauliZ, finSumFinEquiv, Fin.addCases, Matrix.diagonal]
theorem g66c_sbX : sumBlock pauliXFin pauliXFin = !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sumBlock, pauliXFin, QAlgorithms.pauliX, finSumFinEquiv, Fin.addCases]

theorem g66c_unit (a b : ℂ) (hnorm : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 / 2) :
    qubitCompletion a b ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  have ha : a * conj a = (Complex.normSq a : ℂ) := Complex.mul_conj a
  have hb : b * conj b = (Complex.normSq b : ℂ) := Complex.mul_conj b
  have hR : Complex.normSq a + Complex.normSq b = 1 / 2 := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]; exact hnorm
  have hC : ((Complex.normSq a + Complex.normSq b : ℝ) : ℂ) = 1 / 2 := by
    rw [hR]; push_cast; ring
  push_cast at hC
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [qubitCompletion, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply] <;>
    first | ring1 | linear_combination 2*ha + 2*hb + 2*hC

theorem g66c_impl (a b : ℂ) (hnorm : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 / 2) :
    ImplementsPOVM (qubitColumns a b) (qubitCompletion a b).conjTranspose
      (Fin.castAdd 2) := by
  refine ⟨?_, ?_⟩
  · have := g66c_unit a b hnorm
    exact Unitary.star_mem this
  · intro rho _ o
    fin_cases o <;>
    simp [qubitCompletion, qubitColumns, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, coordinateInclusion, columnEffect, QAlgorithms.pureDensity, Matrix.trace,
      Fin.castAdd] <;> ring

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

theorem solution (a b : ℂ) (hnorm : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 / 2) :
    qubitCompletion a b ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
    (∀ i j, qubitCompletion a b (Fin.castAdd 2 i) j = qubitColumns a b i j) ∧
    sumBlock pauliZFin pauliZFin * qubitCompletion a b = qubitCompletion a b * pauliRZ ∧
    sumBlock pauliXFin pauliXFin * qubitCompletion a b = qubitCompletion a b * pauliRX ∧
    ImplementsPOVM (qubitColumns a b) (qubitCompletion a b).conjTranspose
      (Fin.castAdd 2) := by
  refine ⟨g66c_unit a b hnorm, ?_, ?_, ?_, g66c_impl a b hnorm⟩
  · intro i j; fin_cases i <;> fin_cases j <;> rfl
  · rw [g66c_sbZ]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [qubitCompletion, pauliRZ, Matrix.mul_apply, Fin.sum_univ_four]
  · rw [g66c_sbX]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [qubitCompletion, pauliRX, Matrix.mul_apply, Fin.sum_univ_four]

end
