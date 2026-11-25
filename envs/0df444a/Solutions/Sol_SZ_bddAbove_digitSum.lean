-- Prove2me | solution 1 for SZ.bddAbove_digitSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:41:04.925476+00:00
-- url     : https://prove2.me/submissions/16b0ca69-2d90-49d4-a028-09aa7e3e74b9

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
theorem _root_.solution (h : IsDigits m d) : BddAbove (Set.range (digitSum m d)) :=
  ⟨1, by rintro _ ⟨k, rfl⟩; exact digitSum_le_one h k⟩
end SZ
