-- Prove2me | solution 1 for SparsificationLemma.Cal.log_le_yC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:50:18.595436+00:00
-- url     : https://prove2.me/submissions/bc43388c-21e9-4c0a-856b-07e28a4e4a4e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_SparsificationLemma_Cal_Thr
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_SparsificationLemma_Shrink
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsifyWidthK_Thresholds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Facts

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
namespace SparsificationLemma.Cal
theorem _root_.solution {α k : ℕ} (hα : 1 ≤ α) (hk : 2 ≤ k) :
    (((k - 1 : ℕ) : ℝ) / (α : ℝ)) * Real.logb 2 (Real.exp 1 * (α : ℝ) * ((4 * (32 * α) ^ (k - 2) : ℕ) : ℝ)) ≤ yC k α := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have ha : (1 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have he0 := Real.exp_pos 1
  have hq : (0 : ℝ) < 32 * (α : ℝ) := by positivity
  have hp : (0 : ℝ) < (32 * (α : ℝ)) ^ m := by positivity
  have h1 : Real.exp 1 * (α : ℝ) * ((4 * (32 * α) ^ (m + 2 - 2) : ℕ) : ℝ) ≤ (32 * (α : ℝ)) ^ (m + 1) := by
    rw [show m + 2 - 2 = m by omega, pow_succ]
    push_cast
    have : Real.exp 1 * (α : ℝ) * 4 ≤ 32 * (α : ℝ) := by nlinarith
    calc Real.exp 1 * (α : ℝ) * (4 * (32 * (α : ℝ)) ^ m) = (Real.exp 1 * (α : ℝ) * 4) * (32 * (α : ℝ)) ^ m := by ring
      _ ≤ 32 * (α : ℝ) * (32 * (α : ℝ)) ^ m := mul_le_mul_of_nonneg_right this hp.le
      _ = (32 * (α : ℝ)) ^ m * (32 * (α : ℝ)) := by ring
  have h0 : 0 < Real.exp 1 * (α : ℝ) * ((4 * (32 * α) ^ (m + 2 - 2) : ℕ) : ℝ) := by
    have : (0 : ℝ) < ((4 * (32 * α) ^ (m + 2 - 2) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (by norm_num) (Nat.pow_pos (by omega))
    positivity
  have h2 := Real.logb_le_logb_of_le one_lt_two h0 h1
  rw [Real.logb_pow] at h2
  have hc : ((m + 2 - 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
    rw [show m + 2 - 1 = m + 1 by omega]; push_cast; ring
  have hc0 : (0 : ℝ) ≤ ((m : ℝ) + 1) / (α : ℝ) := by positivity
  rw [hc, yC]
  calc ((m : ℝ) + 1) / (α : ℝ) * Real.logb 2 (Real.exp 1 * (α : ℝ) * ((4 * (32 * α) ^ (m + 2 - 2) : ℕ) : ℝ))
      ≤ ((m : ℝ) + 1) / (α : ℝ) * (((m + 1 : ℕ) : ℝ) * Real.logb 2 (32 * (α : ℝ))) := mul_le_mul_of_nonneg_left h2 hc0
    _ = 32 * (((m + 2 : ℕ) : ℝ) - 1) ^ 2 * Real.logb 2 (32 * (α : ℝ)) / (32 * (α : ℝ)) := by
        push_cast
        field_simp
        ring
end SparsificationLemma.Cal
