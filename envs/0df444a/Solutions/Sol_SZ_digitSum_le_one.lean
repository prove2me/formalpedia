-- Prove2me | solution 1 for SZ.digitSum_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:37:28.374835+00:00
-- url     : https://prove2.me/submissions/cb86c0f3-4d9d-4659-8224-0db4342c9111

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity
import Theorems.Thm_P2M_SZ_IsDigits_pow_pos__7f25d03f067c
import Theorems.Thm_SZ_digitSum_zero
import Theorems.Thm_SZ_digitSum_le_of_le

set_option autoImplicit false
open SZ
open Finset Filter Topology
variable {m : ℕ} {d : ℕ → ℤ}
namespace SZ
theorem _root_.solution (h : IsDigits m d) (k : ℕ) : digitSum m d k ≤ 1 := by
  have hb := digitSum_le_of_le h (Nat.zero_le k)
  have h1 : (0 : ℝ) < 1 / (m : ℝ) ^ k := one_div_pos.mpr (h.pow_pos' k)
  rw [digitSum_zero, pow_zero] at hb
  linarith
end SZ
