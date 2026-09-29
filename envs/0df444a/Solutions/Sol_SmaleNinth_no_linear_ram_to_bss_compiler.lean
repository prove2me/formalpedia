-- Prove2me | solution 1 for SmaleNinth.no_linear_ram_to_bss_compiler
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T01:24:02.731626+00:00
-- url     : https://prove2.me/submissions/e60451fa-7cd8-4e7b-81f4-788953a8ace0

import Theorems.Thm_SmaleNinth_real_ram_decides_one_variable_lp_linear
import Theorems.Thm_SmaleNinth_bss_one_variable_lp_no_linear_program
import Mathlib.Tactic

/-!
# No compilation of the pointer machine into the tape machine with linear overhead

One-variable LP feasibility separates the two models: it is decided in `O(m)`
steps by a pointer machine and in no fewer than `ω(m)` steps by any tape
machine, so a compiler with constant-factor overhead would contradict the
tape lower bound.
-/

open SmaleNinth Matrix LinearOptimization

theorem solution :
    ¬ ∀ (R : RAMProgram), ∃ (P : BSSProgram) (K : ℕ), ∀ (x : ℤ → ℝ), (∀ c : ℤ, c < 0 → x c = 0) →
        ∀ (T : ℕ) (b : Bool),
          RAMDecidesInTime R x T b → BSSDecidesInTime P x (K * (T + 1)) b := by
  intro hcomp
  -- the linear-time pointer-machine algorithm for one-variable LP
  obtain ⟨R, C, hR⟩ := SmaleNinth.real_ram_decides_one_variable_lp_linear
  -- its hypothetical linear-overhead compilation
  obtain ⟨P, K, hP⟩ := hcomp R
  -- contradicts the tape lower bound with the constant `K (C + 1)`
  refine SmaleNinth.bss_one_variable_lp_no_linear_program P (K * (C + 1)) ?_
  intro m A b
  obtain ⟨result, hdec, hiff⟩ := hR m A b
  have hneg : ∀ c : ℤ, c < 0 → encodeLP A b c = 0 := by
    intro c hc
    unfold encodeLP
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_neg (by omega)]
  have hbss := hP (encodeLP A b) hneg (C * (m + 1)) result hdec
  refine ⟨result, ?_, hiff⟩
  obtain ⟨t, ht, hhalt⟩ := hbss
  exact ⟨t, le_trans ht (by nlinarith), hhalt⟩
