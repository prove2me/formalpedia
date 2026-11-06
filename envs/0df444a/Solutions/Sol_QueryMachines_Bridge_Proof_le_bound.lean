-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.le_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:05:39.078729+00:00
-- url     : https://prove2.me/submissions/13f0e888-440c-4ebd-a25a-68f91b3475a5

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
theorem _root_.solution {e : ℝ} {K C₀ lam : ℕ} (B : ℕ) (he : 0 ≤ e) (hC : 1 ≤ C₀) (hK : 1 ≤ K) (hlam : 1 ≤ lam) : (K : ℝ) * ((lam : ℝ) + B) ≤ bound e K C₀ lam B := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hl' : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hB' : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hx : 1 ≤ (K : ℝ) * ((lam : ℝ) + B) := by nlinarith
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * lam) := Real.one_le_rpow one_le_two (by positivity)
  have h2 : (K : ℝ) * ((lam : ℝ) + B) ≤ ((K : ℝ) * ((lam : ℝ) + B)) ^ (C₀ * K ^ 2) := le_self_pow₀ hx (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
  unfold bound
  calc (K : ℝ) * ((lam : ℝ) + B) = 1 * ((K : ℝ) * ((lam : ℝ) + B)) := (one_mul _).symm
    _ ≤ _ := mul_le_mul h1 h2 (by linarith) (by linarith)
end QueryMachines.Bridge.Proof
