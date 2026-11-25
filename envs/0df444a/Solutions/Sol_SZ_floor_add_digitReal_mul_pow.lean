-- Prove2me | solution 1 for SZ.floor_add_digitReal_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:24:44.05075+00:00
-- url     : https://prove2.me/submissions/fc05fed5-b442-4758-8bb3-6a898427b2d7

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity
import Theorems.Thm_P2M_SZ_IsDigits_pow_pos__7f25d03f067c
import Theorems.Thm_SZ_digitSum_le_digitReal
import Theorems.Thm_SZ_digitReal_lt_digitSum_add
import Theorems.Thm_SZ_digitSum_mul_pow

set_option autoImplicit false
open SZ
open Finset Filter Topology
variable {m : ℕ} {d : ℕ → ℤ}
namespace SZ
theorem _root_.solution (h : IsDigits m d) (N : ℤ) (s : ℕ) {i₀ : ℕ}
    (hk : s ≤ i₀) (hsmall : d i₀ ≤ (m : ℤ) - 2) :
    ⌊((N : ℝ) + digitReal m d) * (m : ℝ) ^ s⌋
      = N * (m : ℤ) ^ s + ∑ i ∈ Finset.range s, d i * (m : ℤ) ^ (s - (i + 1)) := by
  have hp : (0 : ℝ) < (m : ℝ) ^ s := h.pow_pos' _
  have hlo : digitSum m d s ≤ digitReal m d := digitSum_le_digitReal h s
  have hhi : digitReal m d < digitSum m d s + 1 / (m : ℝ) ^ s :=
    digitReal_lt_digitSum_add h hk hsmall
  have hmul := digitSum_mul_pow h s
  have hone : (1 / (m : ℝ) ^ s) * (m : ℝ) ^ s = 1 := by field_simp
  have hZ : ((N * (m : ℤ) ^ s + ∑ i ∈ Finset.range s, d i * (m : ℤ) ^ (s - (i + 1)) : ℤ) : ℝ)
      = ((N : ℝ) + digitSum m d s) * (m : ℝ) ^ s := by
    rw [add_mul, hmul]; push_cast; ring
  rw [Int.floor_eq_iff, hZ]
  refine ⟨by nlinarith, by nlinarith⟩
end SZ
