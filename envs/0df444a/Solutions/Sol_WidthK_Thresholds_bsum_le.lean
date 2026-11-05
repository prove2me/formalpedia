-- Prove2me | solution 1 for WidthK.Thresholds.bsum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:23:22.413229+00:00
-- url     : https://prove2.me/submissions/f643393c-f15e-4732-a7d6-385df58c0b1b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_StepMachines_Math_SparsifyCount
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_SparsifyWidthK_Thresholds
import Theorems.Thm_P2M_WidthK_Thresholds_theta_succ__5d83f02a22b6
import Theorems.Thm_P2M_WidthK_Thresholds_bsum_succ__02c5a6e09a02
import Theorems.Thm_WidthK_Thresholds_one_le_theta
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open WidthK WidthK.Thresholds
open Finset
namespace WidthK.Thresholds
theorem _root_.solution {τ : ℕ} (hτ : 1 ≤ τ) (i : ℕ) : bsum τ i ≤ 2 * theta τ i := by
  cases i with
  | zero => exact le_refl _
  | succ i =>
    have h1 := one_le_theta hτ i
    rw [bsum_succ', theta_succ']
    calc bsum τ i * (1 + 2 * theta τ i) ≤ bsum τ i * (4 * τ * theta τ i) := by
          refine Nat.mul_le_mul_left _ ?_
          have : 4 * 1 * theta τ i ≤ 4 * τ * theta τ i :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hτ)
          omega
      _ = 2 * (2 * τ * theta τ i * bsum τ i) := by ring
end WidthK.Thresholds
