-- Prove2me | solution 1 for SZ.IsDigits.one_lt_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:12:19.165949+00:00
-- url     : https://prove2.me/submissions/b99126ed-43d5-41ad-bd90-f7d21060cde6

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity

set_option autoImplicit false
open SZ
open Finset Filter Topology
open SZ.IsDigits
variable {m : ℕ} {d : ℕ → ℤ}
namespace SZ.IsDigits
theorem _root_.solution (h : IsDigits m d) : (1 : ℝ) < (m : ℝ) := by
  exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) h.two_le
end SZ.IsDigits
