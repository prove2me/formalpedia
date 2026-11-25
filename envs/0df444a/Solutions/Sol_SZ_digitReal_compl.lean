-- Prove2me | solution 1 for SZ.digitReal_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:57:07.612302+00:00
-- url     : https://prove2.me/submissions/d6c3e205-e9b5-4ae6-ac03-08234cd26cec

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity
import Theorems.Thm_SZ_IsDigits_one_lt_cast
import Theorems.Thm_SZ_IsDigits_cast_pos
import Theorems.Thm_P2M_SZ_IsDigits_pow_pos__7f25d03f067c
import Theorems.Thm_SZ_digitSum_succ
import Theorems.Thm_SZ_digitSum_tendsto

set_option autoImplicit false
open SZ
open Finset Filter Topology
variable {m : ℕ} {d : ℕ → ℤ}
namespace SZ
theorem _root_.solution (h : IsDigits m d) :
    digitReal m (fun i => (m : ℤ) - 1 - d i) = 1 - digitReal m d := by
  have hc : IsDigits m (fun i => (m : ℤ) - 1 - d i) :=
    { two_le := h.two_le
      nonneg := fun i => by have := h.le_sub_one i; omega
      le_sub_one := fun i => by have := h.nonneg i; omega }
  -- the partial sums of the complement
  have hpartial : ∀ k, digitSum m (fun i => (m : ℤ) - 1 - d i) k
      = (1 - 1 / (m : ℝ) ^ k) - digitSum m d k := by
    intro k
    induction k with
    | zero => simp [digitSum]
    | succ k ih =>
      rw [digitSum_succ, digitSum_succ, ih]
      have hp : (0 : ℝ) < (m : ℝ) ^ k := h.pow_pos' _
      have hp1 : (0 : ℝ) < (m : ℝ) ^ (k + 1) := h.pow_pos' _
      push_cast
      field_simp
      ring
  have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / (m : ℝ) ^ k) atTop (𝓝 0) := by
    have : ∀ k : ℕ, (1 : ℝ) / (m : ℝ) ^ k = (1 / (m : ℝ)) ^ k := fun k => by
      rw [div_pow, one_pow]
    simp only [this]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      ((div_lt_one h.cast_pos).mpr h.one_lt_cast)
  have hlim : Tendsto (digitSum m (fun i => (m : ℤ) - 1 - d i)) atTop
      (𝓝 (1 - digitReal m d)) := by
    have hfun : digitSum m (fun i => (m : ℤ) - 1 - d i)
        = fun k => (1 - 1 / (m : ℝ) ^ k) - digitSum m d k := funext hpartial
    rw [hfun]
    have hone : (1 : ℝ) - digitReal m d = (1 - 0) - digitReal m d := by ring
    rw [hone]
    exact ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub h0).sub
      (digitSum_tendsto h)
  exact tendsto_nhds_unique (digitSum_tendsto hc) hlim
end SZ
