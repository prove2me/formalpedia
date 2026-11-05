-- Prove2me | solution 1 for WidthK.stLeafCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:56:57.545179+00:00
-- url     : https://prove2.me/submissions/6cb849cc-8933-421f-aa99-74640f136517

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
import Theorems.Thm_WidthK_Thresholds_add_two_le_bsum
import Theorems.Thm_WidthK_Thresholds_sum_choose_le_two_rpow
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open WidthK
open Finset Thresholds
namespace WidthK
theorem _root_.solution : StLeafCount := by
  intro k τ ε hτ h n
  exact sum_choose_le_two_rpow hτ (by have := add_two_le_bsum hτ k; omega) h n
end WidthK
