-- Prove2me | solution 2 for Tegmark.pde_trichotomy
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:43:48.125216+00:00
-- url     : https://prove2.me/submissions/f9f683f6-8f8d-432d-afb8-012e355902db

import Mathlib
import Definitions.Def_Tegmark_sig
import Definitions.Def_Tegmark_phys
import Definitions.Def_Tegmark_ensemble
set_option autoImplicit false

open Tegmark

theorem solution (n m : ℕ) :
    (pdeClass n m = PDEClass.elliptic ↔ n = 0 ∨ m = 0) ∧
    (pdeClass n m = PDEClass.hyperbolic ↔ n ≠ 0 ∧ m ≠ 0 ∧ (n = 1 ∨ m = 1)) ∧
    (pdeClass n m = PDEClass.ultrahyperbolic ↔ 2 ≤ n ∧ 2 ≤ m) := by
  unfold pdeClass
  split_ifs with h1 h2 <;> simp <;> omega

