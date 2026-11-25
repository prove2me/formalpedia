-- Prove2me | solution 1 for SZ.IsDigits.cast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:17:25.153315+00:00
-- url     : https://prove2.me/submissions/94c93505-c824-474f-a47d-6b8e4e20e84f

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity
import Theorems.Thm_SZ_IsDigits_cast_pos

set_option autoImplicit false
open SZ
open Finset Filter Topology
open SZ.IsDigits
variable {m : ℕ} {d : ℕ → ℤ}
namespace SZ.IsDigits
theorem _root_.solution (h : IsDigits m d) : (m : ℝ) ≠ 0 := ne_of_gt h.cast_pos
end SZ.IsDigits
