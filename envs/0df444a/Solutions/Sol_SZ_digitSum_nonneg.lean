-- Prove2me | solution 1 for SZ.digitSum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:23:09.10881+00:00
-- url     : https://prove2.me/submissions/902b5069-61ee-46f5-b8ac-dbcb9666e7f1

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity
import Theorems.Thm_SZ_digitSum_zero
import Theorems.Thm_SZ_digitSum_monotone

set_option autoImplicit false
open SZ
open Finset Filter Topology
variable {m : ℕ} {d : ℕ → ℤ}
namespace SZ
theorem _root_.solution (h : IsDigits m d) (k : ℕ) : 0 ≤ digitSum m d k := by
  simpa [digitSum_zero] using digitSum_monotone h (Nat.zero_le k)
end SZ
