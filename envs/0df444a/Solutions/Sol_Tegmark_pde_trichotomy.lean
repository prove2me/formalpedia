-- Prove2me | solution 1 for Tegmark.pde_trichotomy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:07:17.351427+00:00
-- url     : https://prove2.me/submissions/3344d4b4-7c05-4035-bd56-ea60e9358935

import Mathlib
import Definitions.Def_Tegmark_sig
import Definitions.Def_Tegmark_phys
import Definitions.Def_Tegmark_ensemble
open Tegmark

theorem solution (n m : ℕ) :
    (pdeClass n m = PDEClass.elliptic ↔ n = 0 ∨ m = 0) ∧
    (pdeClass n m = PDEClass.hyperbolic ↔ n ≠ 0 ∧ m ≠ 0 ∧ (n = 1 ∨ m = 1)) ∧
    (pdeClass n m = PDEClass.ultrahyperbolic ↔ 2 ≤ n ∧ 2 ≤ m) := by
  unfold pdeClass
  by_cases h0 : n = 0 ∨ m = 0
  · rw [if_pos h0]; refine ⟨by simp [h0], ?_, ?_⟩ <;> simp only [reduceCtorEq, false_iff] <;> omega
  · rw [if_neg h0]
    by_cases h1 : n = 1 ∨ m = 1
    · rw [if_pos h1]; refine ⟨?_, ?_, ?_⟩ <;> simp only [reduceCtorEq, false_iff, true_iff] <;> omega
    · rw [if_neg h1]; refine ⟨?_, ?_, ?_⟩ <;> simp only [reduceCtorEq, false_iff, true_iff] <;> omega
