-- Prove2me | solution 1 for SiegelFields.neg_two_det_eq_trace_sq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T16:37:45.031483+00:00
-- url     : https://prove2.me/submissions/0851e383-b823-4644-851c-2d1d665dbb13

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

theorem solution (M : Matrix (Fin 2) (Fin 2) ℂ) :
    -2 * M.det = trace (M * M) - (trace M) ^ 2 := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring
