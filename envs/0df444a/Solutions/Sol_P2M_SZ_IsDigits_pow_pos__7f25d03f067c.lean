-- Prove2me | solution 1 for P2M_SZ_IsDigits_pow_pos__7f25d03f067c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:17:22.929733+00:00
-- url     : https://prove2.me/submissions/45ce5144-ca69-4290-8973-9b52536a380f

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
theorem _root_.solution (h : IsDigits m d) (k : ℕ) : (0 : ℝ) < (m : ℝ) ^ k := pow_pos h.cast_pos k
end SZ.IsDigits
