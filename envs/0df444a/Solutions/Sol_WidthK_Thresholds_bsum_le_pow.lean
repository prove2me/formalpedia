-- Prove2me | solution 1 for WidthK.Thresholds.bsum_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:38:57.240245+00:00
-- url     : https://prove2.me/submissions/d60107e3-6c9a-4c7d-a37d-c44a55ee58de

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
import Theorems.Thm_WidthK_Thresholds_bsum_le
import Theorems.Thm_WidthK_Thresholds_sq_mul_theta_le
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open WidthK WidthK.Thresholds
open Finset
namespace WidthK.Thresholds
theorem _root_.solution {τ : ℕ} (hτ : 4 ≤ τ) (i : ℕ) : bsum τ i ≤ τ ^ 2 ^ (i + 1) := by
  refine le_trans (bsum_le (by omega) i) (le_trans (Nat.mul_le_mul_right _ ?_) (sq_mul_theta_le hτ i))
  nlinarith
end WidthK.Thresholds
