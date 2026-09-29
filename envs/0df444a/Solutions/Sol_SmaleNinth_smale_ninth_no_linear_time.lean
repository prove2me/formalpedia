-- Prove2me | solution 1 for SmaleNinth.smale_ninth_no_linear_time
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T18:37:32.254387+00:00
-- url     : https://prove2.me/submissions/6df23401-9c4c-459d-afbb-ae51bf4720d9

import Theorems.Thm_SmaleNinth_bss_one_variable_lp_no_linear_program
import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_BSSMachine

/-!
Degree-one exclusion for the goal of the mission: a linear budget
`C·(mn+m+2)` restricted to `n = 1` is the linear budget `2C·(m+1)` of the
one-variable problem, which is excluded.
-/

open SmaleNinth Matrix LinearOptimization

theorem solution (P : BSSProgram) (C : ℕ) :
    ¬ ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          BSSDecidesInTime P (encodeLP A b) (C * (m * n + m + 2)) result ∧
          (result = true ↔ (polyhedron A b).Nonempty) := by
  intro h
  apply SmaleNinth.bss_one_variable_lp_no_linear_program P (2 * C)
  intro m A b
  obtain ⟨result, hdec, hres⟩ := h m 1 A b
  refine ⟨result, ?_, hres⟩
  have : C * (m * 1 + m + 2) = 2 * C * (m + 1) := by ring
  rw [this] at hdec
  exact hdec
