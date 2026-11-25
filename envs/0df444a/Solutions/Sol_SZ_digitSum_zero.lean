-- Prove2me | solution 1 for SZ.digitSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:44:08.032464+00:00
-- url     : https://prove2.me/submissions/11898067-cc5c-4a06-81b1-735cb06ff8fc

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
variable {m : ℕ} {d : ℕ → ℤ}
namespace SZ
theorem _root_.solution (m : ℕ) (d : ℕ → ℤ) : digitSum m d 0 = 0 := by
  simp [digitSum]
end SZ
