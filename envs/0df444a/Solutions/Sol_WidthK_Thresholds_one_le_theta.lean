-- Prove2me | solution 1 for WidthK.Thresholds.one_le_theta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:16:24.987197+00:00
-- url     : https://prove2.me/submissions/6c6b5370-b054-4a3b-8c96-ab69159ae967

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
import Theorems.Thm_WidthK_Thresholds_two_le_bsum
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open WidthK WidthK.Thresholds
open Finset
namespace WidthK.Thresholds
theorem _root_.solution {τ : ℕ} (hτ : 1 ≤ τ) (i : ℕ) : 1 ≤ theta τ i := by
  induction i with
  | zero => exact le_refl _
  | succ i ih =>
    rw [theta_succ']
    have := two_le_bsum τ i
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
end WidthK.Thresholds
