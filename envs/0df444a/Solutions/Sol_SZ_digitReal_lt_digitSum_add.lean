-- Prove2me | solution 1 for SZ.digitReal_lt_digitSum_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:23:12.888804+00:00
-- url     : https://prove2.me/submissions/89adeb62-4bd5-433b-a601-56b4b1f7af1e

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
import Theorems.Thm_SZ_digitSum_monotone
import Theorems.Thm_SZ_digitSum_le_of_le
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
theorem _root_.solution (h : IsDigits m d) {k i₀ : ℕ} (hk : k ≤ i₀)
    (hsmall : d i₀ ≤ (m : ℤ) - 2) :
    digitReal m d < digitSum m d k + 1 / (m : ℝ) ^ k := by
  have hp0 : (0 : ℝ) < (m : ℝ) ^ i₀ := h.pow_pos' _
  have hp1 : (0 : ℝ) < (m : ℝ) ^ (i₀ + 1) := h.pow_pos' _
  have hmar : (0 : ℝ) < 1 / (m : ℝ) ^ (i₀ + 1) := one_div_pos.mpr hp1
  have hdi : (d i₀ : ℝ) ≤ (m : ℝ) - 2 := by exact_mod_cast hsmall
  -- the step across the small digit gains a full `2 / m^{i₀+1}`
  have key : (d i₀ : ℝ) / (m : ℝ) ^ (i₀ + 1)
      ≤ 1 / (m : ℝ) ^ i₀ - 2 / (m : ℝ) ^ (i₀ + 1) := by
    rw [tail_id h.cast_ne_zero i₀ 2]
    gcongr
  rw [show (2 : ℝ) / (m : ℝ) ^ (i₀ + 1)
      = 1 / (m : ℝ) ^ (i₀ + 1) + 1 / (m : ℝ) ^ (i₀ + 1) from by ring] at key
  have h2 := digitSum_le_of_le h hk
  -- hence: the partial sum at `i₀ + 1` is already `1/m^{i₀+1}` below the naive bound
  have hstep : digitSum m d (i₀ + 1)
      ≤ digitSum m d k + 1 / (m : ℝ) ^ k
          - (1 / (m : ℝ) ^ (i₀ + 1) + 1 / (m : ℝ) ^ (i₀ + 1)) := by
    rw [digitSum_succ]
    linarith
  refine lt_of_le_of_lt (ciSup_le fun j => ?_) (by linarith : digitSum m d k + 1 / (m : ℝ) ^ k
      - 1 / (m : ℝ) ^ (i₀ + 1) < digitSum m d k + 1 / (m : ℝ) ^ k)
  rcases le_or_gt j (i₀ + 1) with hj | hj
  · have := digitSum_monotone h hj
    linarith
  · have h4 := digitSum_le_of_le h hj.le
    have h5 : (0 : ℝ) < 1 / (m : ℝ) ^ j := one_div_pos.mpr (h.pow_pos' j)
    linarith
end SZ
