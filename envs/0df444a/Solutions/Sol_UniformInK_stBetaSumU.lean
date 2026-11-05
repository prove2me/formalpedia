-- Prove2me | solution 1 for UniformInK.stBetaSumU
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:28:20.105877+00:00
-- url     : https://prove2.me/submissions/411ee30a-1b64-471a-b1f8-6caa7168e90f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Mathlib.Tactic.Ring
import Definitions.Def_UniformInK_Spars_Thresholds
set_option autoImplicit false
section
section
open UniformInK
open Finset

theorem solution : StBetaSumU := by
  intro τ k hτ
  have beta_le : ∀ j : ℕ, betaSU τ j ≤ τ ^ (2 * j) := by
    intro j
    cases j with
    | zero => simp [betaSU]
    | succ j =>
      simp only [betaSU]
      calc
        4 * τ ^ (2 * j) ≤ τ * τ * τ ^ (2 * j) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul hτ hτ)
        _ = τ ^ (2 * (j + 1)) := by ring
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, bsumU]
    rw [bsumU] at ih
    calc
      ∑ i ∈ range k, betaSU τ i + betaSU τ k ≤ τ ^ (2 * k) + τ ^ (2 * k) :=
        Nat.add_le_add ih (beta_le k)
      _ = 2 * 1 * τ ^ (2 * k) := by ring
      _ ≤ τ * τ * τ ^ (2 * k) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hτ (by omega))
      _ = τ ^ (2 * (k + 1)) := by ring
