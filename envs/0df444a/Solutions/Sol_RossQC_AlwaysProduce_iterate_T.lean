-- Prove2me | solution 1 for RossQC.AlwaysProduce.iterate_T
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:58:45.907909+00:00
-- url     : https://prove2.me/submissions/78a98752-ea3c-4c54-8a72-c7a5b6f4d1da

import Mathlib
import Definitions.Def_RossQC_AlwaysProduce_Model
open RossQC.AlwaysProduce

theorem solution (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ∀ (n : ℕ) (P : ℝ), P ∈ Set.Icc (0 : ℝ) 1 →
      (M.T^[n]) P = 1 - (1 - P) * (1 - M.π) ^ n := by
  intro n P hP
  have hi : ∀ n : ℕ, (M.T^[n]) P = 1 - (1 - P) * (1 - M.π)^n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Model.T, pow_succ]
      ring
  exact hi n

#print axioms solution
