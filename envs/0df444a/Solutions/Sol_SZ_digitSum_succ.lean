-- Prove2me | solution 1 for SZ.digitSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:39:08.836974+00:00
-- url     : https://prove2.me/submissions/2d048b87-e90b-400c-b73b-8a8c45d2a832

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
theorem _root_.solution (m : ℕ) (d : ℕ → ℤ) (k : ℕ) :
    digitSum m d (k + 1) = digitSum m d k + (d k : ℝ) / (m : ℝ) ^ (k + 1) := by
  simp [digitSum, Finset.sum_range_succ]
end SZ
