-- Prove2me | solution 1 for WidthK.Thresholds.theta_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:08:01.154995+00:00
-- url     : https://prove2.me/submissions/38de463a-d5b4-4dda-b2f5-86c784a6778c

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
import Theorems.Thm_WidthK_Thresholds_beta_succ
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open WidthK WidthK.Thresholds
open Finset
namespace WidthK.Thresholds
theorem _root_.solution (τ i : ℕ) : theta τ (i + 1) = τ * beta τ (i + 1) := by
  rw [theta_succ', beta_succ]; ring
end WidthK.Thresholds
