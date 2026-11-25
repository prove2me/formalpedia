-- Prove2me | solution 1 for SZ.IsDigits.cast_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:15:11.847395+00:00
-- url     : https://prove2.me/submissions/6793a0c2-24ba-47ff-ba6c-3da480237828

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity
import Theorems.Thm_SZ_IsDigits_one_lt_cast

set_option autoImplicit false
open SZ
open Finset Filter Topology
open SZ.IsDigits
variable {m : ℕ} {d : ℕ → ℤ}
namespace SZ.IsDigits
theorem _root_.solution (h : IsDigits m d) : (0 : ℝ) < (m : ℝ) := lt_trans zero_lt_one h.one_lt_cast
end SZ.IsDigits
