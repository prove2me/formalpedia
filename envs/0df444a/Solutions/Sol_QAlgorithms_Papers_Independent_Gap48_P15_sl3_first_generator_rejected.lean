-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P15.sl3_first_generator_rejected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T23:59:33.901903+00:00
-- url     : https://prove2.me/submissions/77fc6322-0b88-4935-bfff-d4daadfeef55

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P15
open QAlgorithms.Papers.Independent.Gap48.P15

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reuse Mathlib Matrix and Matrix.single directly. Natural one-based
-- coordinates are restricted to Fin coordinates with Matrix.submatrix.

theorem g74a_sl3_br :
    ⁅((Matrix.single 1 2 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1)), (((Matrix.single 1 2 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1))).transpose⁆ =
      Matrix.diagonal ![(1 : ℝ), -1, 0] := by
  rw [Ring.lie_def]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.single, Matrix.submatrix, Matrix.diagonal]

/-- The first Bsl(3) matrix b1=F12 fails Star, with the exact displayed commutator.
Source: PDF pp. 10-11. This is failure of the guard, not a Cartan nonexistence claim. -/
theorem solution :
    ⁅((Matrix.single 1 2 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1)), (((Matrix.single 1 2 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1))).transpose⁆ =
      Matrix.diagonal ![(1 : ℝ), -1, 0] ∧
    ¬ star ![((Matrix.single 1 2 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1))] := by
  refine ⟨g74a_sl3_br, ?_⟩
  intro h
  have h0 := h 0 0 le_rfl
  simp only [Matrix.cons_val_zero] at h0
  rw [g74a_sl3_br] at h0
  have := congrFun (congrFun h0 0) 0
  simp [Matrix.diagonal] at this
