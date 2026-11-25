-- Prove2me | solution 1 for SZ.digitReal_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:42:16.599593+00:00
-- url     : https://prove2.me/submissions/a4288e18-e604-4886-9ed5-4ad8f9e1309c

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity
import Theorems.Thm_SZ_digitSum_le_one

set_option autoImplicit false
open SZ
open Finset Filter Topology
variable {m : ℕ} {d : ℕ → ℤ}
namespace SZ
theorem _root_.solution (h : IsDigits m d) : digitReal m d ≤ 1 :=
  ciSup_le (digitSum_le_one h)
end SZ
