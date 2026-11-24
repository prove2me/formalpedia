-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.entry_mul_single_mul
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T01:33:55.006931+00:00
-- url     : https://prove2.me/submissions/5b397900-49d2-45ce-b859-f64794f1dfa2

import Mathlib
variable {n : ℕ}


theorem solution (M : Matrix (Fin n) (Fin n) ℂ) (a b k l : Fin n) :
    (M * Matrix.single l k (1 : ℂ) * M) a b = M a l * M k b := by
  classical
  simp only [Matrix.mul_apply,Matrix.single_apply]
  simp [ite_and, Finset.mul_sum, Finset.sum_mul, eq_comm]
