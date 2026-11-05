-- Prove2me | solution 1 for WidthK.Thresholds.add_two_le_bsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:54:09.439296+00:00
-- url     : https://prove2.me/submissions/10a6066e-addc-49a5-9aad-e07797ee4df0

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
import Theorems.Thm_WidthK_Thresholds_beta_succ
import Theorems.Thm_WidthK_Thresholds_bsum_succ
import Theorems.Thm_WidthK_Thresholds_two_le_bsum
import Theorems.Thm_WidthK_Thresholds_one_le_theta
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open WidthK WidthK.Thresholds
open Finset
namespace WidthK.Thresholds
theorem _root_.solution {τ : ℕ} (hτ : 1 ≤ τ) (i : ℕ) : i + 2 ≤ bsum τ i := by
  induction i with
  | zero => exact le_refl _
  | succ i ih =>
    have h1 := one_le_theta hτ i
    have h2 : 1 ≤ beta τ (i + 1) := by
      rw [beta_succ]
      have := two_le_bsum τ i
      exact Nat.one_le_iff_ne_zero.2 (by positivity)
    rw [bsum_succ]; omega
end WidthK.Thresholds
