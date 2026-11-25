-- Prove2me | solution 1 for SZ.digitSum_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:19:55.387875+00:00
-- url     : https://prove2.me/submissions/a43c4fad-9a2d-4681-847d-6b3a7d0483cb

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity
import Theorems.Thm_SZ_IsDigits_cast_ne_zero
import Theorems.Thm_P2M_SZ_IsDigits_pow_pos__7f25d03f067c
import Theorems.Thm_SZ_digitSum_succ
section
namespace SZ
open Finset Filter Topology
namespace IsDigits
variable {m : ℕ} {d : ℕ → ℤ}
end IsDigits
variable {m : ℕ} {d : ℕ → ℤ}
private theorem tail_id {M : ℝ} (hM : M ≠ 0) (j : ℕ) (c : ℝ) :
    1 / M ^ j - c / M ^ (j + 1) = (M - c) / M ^ (j + 1) := by
  rw [pow_succ]
  field_simp
end SZ
end

set_option autoImplicit false
open SZ
open Finset Filter Topology
variable {m : ℕ} {d : ℕ → ℤ}
namespace SZ
theorem _root_.solution (h : IsDigits m d) {k j : ℕ} (hkj : k ≤ j) :
    digitSum m d j ≤ digitSum m d k + 1 / (m : ℝ) ^ k - 1 / (m : ℝ) ^ j := by
  induction j, hkj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    rw [digitSum_succ]
    have hp : (0 : ℝ) < (m : ℝ) ^ (j + 1) := h.pow_pos' _
    have hdj : (d j : ℝ) ≤ (m : ℝ) - 1 := by exact_mod_cast h.le_sub_one j
    have key : (d j : ℝ) / (m : ℝ) ^ (j + 1) ≤ 1 / (m : ℝ) ^ j - 1 / (m : ℝ) ^ (j + 1) := by
      rw [tail_id h.cast_ne_zero j 1]
      gcongr
    linarith
end SZ
