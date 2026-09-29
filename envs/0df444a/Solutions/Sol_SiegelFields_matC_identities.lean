-- Prove2me | solution 1 for SiegelFields.matC_identities
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T17:08:09.692029+00:00
-- url     : https://prove2.me/submissions/bab86942-d6f5-4b77-bdba-ddaf415cbf41

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex SiegelFields

theorem solution (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M * matC * Mᵀ * matC = M.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      M + matC * Mᵀ * matC = trace M • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      (trace M = 0 ↔ (M * matC)ᵀ = M * matC) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [matC, Matrix.vecMul_apply_eq_sum, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.smul_apply, one_apply, transpose_apply, of_apply, cons_val_zero, cons_val_succ,
        cons_val_one, head_cons, tail_cons, det_fin_two]
    all_goals
      ring_nf
    all_goals
      rw [I_sq]
    all_goals
      ring
  · constructor
    · ext i j
      fin_cases i <;> fin_cases j
      all_goals
        simp [matC, Matrix.vecMul_apply_eq_sum, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.smul_apply, one_apply, Matrix.add_apply, transpose_apply, of_apply,
          cons_val_zero, cons_val_succ, cons_val_one, head_cons, tail_cons, trace_fin_two]
      all_goals
        ring_nf
      all_goals
        rw [I_sq]
      all_goals
        ring
    · constructor
      · intro h
        have h11 : M 1 1 = -M 0 0 := by
          simp only [trace_fin_two] at h
          linear_combination h
        ext i j
        fin_cases i <;> fin_cases j
        all_goals
          simp [h11, matC, Matrix.vecMul_apply_eq_sum, Matrix.mul_apply, Fin.sum_univ_two,
            transpose_apply, of_apply, cons_val_zero, cons_val_succ, cons_val_one, head_cons,
            tail_cons]
        all_goals
          ring_nf
        all_goals
          rw [I_sq]
        all_goals
          ring
      · intro h
        have eq : M 1 1 * I = -(M 0 0 * I) := by
          simpa [matC, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, of_apply,
            cons_val_zero, cons_val_one, cons_val_succ, head_cons, tail_cons, mul_zero, add_zero,
            zero_add] using congr_fun (congr_fun h 0) 1
        have h2 : M 1 1 * (I * I) = -(M 0 0 * (I * I)) := by
          calc
            M 1 1 * (I * I) = (M 1 1 * I) * I := by ring
            _ = (-(M 0 0 * I)) * I := by rw [eq]
            _ = -(M 0 0 * (I * I)) := by ring
        rw [I_mul_I] at h2
        have h3 : -M 1 1 = M 0 0 := by
          simpa [mul_neg_one, neg_mul, neg_neg] using h2
        simp only [trace_fin_two]
        rw [← h3]
        ring
