-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.bound_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:59:13.607716+00:00
-- url     : https://prove2.me/submissions/a5b85822-bc72-452d-89ec-0320b86ec5e3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_CountedToPadded_Tables
import Definitions.Def_CountedToPadded_Need
import Definitions.Def_CountedToPadded_Pick
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_StepMachines_Prog_SideBasics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_CountedToPadded_Levels

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Eight.SecNetworks Printed CliqueLevels
namespace QueryMachines.Bridge.Proof
theorem _root_.solution {e e' : ℝ} (K C₀ lam : ℕ) {B B' : ℕ} (he : e ≤ e') (hB : B ≤ B') : bound e K C₀ lam B ≤ bound e' K C₀ lam B' := by
  have hB' : (B : ℝ) ≤ B' := by exact_mod_cast hB
  unfold bound
  refine mul_le_mul (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) (pow_le_pow_left₀ (by positivity) ?_ _) (by positivity) (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he (by positivity)) (by positivity)
  · exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
end QueryMachines.Bridge.Proof
