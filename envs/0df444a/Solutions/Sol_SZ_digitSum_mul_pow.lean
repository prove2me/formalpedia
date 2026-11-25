-- Prove2me | solution 1 for SZ.digitSum_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:23:16.872552+00:00
-- url     : https://prove2.me/submissions/84351c74-745d-4a69-94be-9eded93c8334

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity
import Theorems.Thm_SZ_IsDigits_cast_ne_zero

set_option autoImplicit false
open SZ
open Finset Filter Topology
variable {m : ℕ} {d : ℕ → ℤ}
namespace SZ
theorem _root_.solution (h : IsDigits m d) (s : ℕ) :
    digitSum m d s * (m : ℝ) ^ s
      = ((∑ i ∈ Finset.range s, d i * (m : ℤ) ^ (s - (i + 1)) : ℤ) : ℝ) := by
  rw [digitSum, Finset.sum_mul]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i + 1 ≤ s := Finset.mem_range.mp hi
  have hsplit : (m : ℝ) ^ s = (m : ℝ) ^ (i + 1) * (m : ℝ) ^ (s - (i + 1)) := by
    rw [← pow_add, Nat.add_sub_cancel' hi']
  have hm0 : (m : ℝ) ≠ 0 := h.cast_ne_zero
  rw [hsplit]
  field_simp
end SZ
