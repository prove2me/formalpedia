-- Prove2me | solution 1 for SiegelFields.det_vecToMatrix
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T16:59:11.469271+00:00
-- url     : https://prove2.me/submissions/88dcc165-403b-491d-aa19-cc0e8862ef27

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex SiegelFields

theorem solution (v : Fin 3 → ℝ) :
    (vecToMatrix v).det = ((-(1 / 2 : ℝ) * ∑ i, v i ^ 2 : ℝ) : ℂ) ∧
      trace (vecToMatrix v * vecToMatrix v) = ((∑ i, v i ^ 2 : ℝ) : ℂ) := by
  have hsq : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
    rw [inv_pow]
    have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast h2
    rw [this]
    norm_num
  constructor
  · simp only [vecToMatrix, det_smul, det_fin_two, Fintype.card_fin, of_apply, cons_val_zero,
      cons_val_succ, cons_val_one, head_cons, tail_cons, Fin.sum_univ_three]
    ring_nf
    rw [hsq, I_sq]
    push_cast
    ring
  · simp only [vecToMatrix, trace_fin_two, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two,
      Fin.sum_univ_three, of_apply, cons_val_zero, cons_val_succ, cons_val_one, head_cons,
      tail_cons, smul_eq_mul]
    ring_nf
    rw [hsq, I_sq]
    push_cast
    ring
