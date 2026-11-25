-- Prove2me | solution 1 for SZ.digitSum_monotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:19:38.04972+00:00
-- url     : https://prove2.me/submissions/339fb065-3865-44e2-a15c-d8d1d593a53c

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity
import Theorems.Thm_P2M_SZ_IsDigits_pow_pos__7f25d03f067c
import Theorems.Thm_SZ_digitSum_succ

set_option autoImplicit false
open SZ
open Finset Filter Topology
variable {m : ℕ} {d : ℕ → ℤ}
namespace SZ
theorem _root_.solution (h : IsDigits m d) : Monotone (digitSum m d) := by
  refine monotone_nat_of_le_succ fun k => ?_
  rw [digitSum_succ]
  have : (0 : ℝ) ≤ (d k : ℝ) / (m : ℝ) ^ (k + 1) :=
    div_nonneg (by exact_mod_cast h.nonneg k) (h.pow_pos' _).le
  linarith
end SZ
