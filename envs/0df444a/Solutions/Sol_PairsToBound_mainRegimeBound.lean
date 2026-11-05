-- Prove2me | solution 1 for PairsToBound.mainRegimeBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:35:03.810678+00:00
-- url     : https://prove2.me/submissions/022c6fdf-5bb4-411b-a3c8-5284590afedf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_PairsToBound_Arith
import Theorems.Thm_VariableBound_VariablesA_thmVariablesAInParticular


set_option autoImplicit false
section
section
open PairsToBound
open MainTheoremForms VariableBound.Paper
namespace PairsToBound
theorem _root_.solution : MainRegimeBound := by
  intro Idx _ S e C₀ Q a he M C' hM
  obtain ⟨C, hC⟩ := VariableBound.VariablesA.thmVariablesAInParticular Idx S e C₀ Q (1 / 2) a (by norm_num) (fun l => by rw [← Real.sqrt_eq_rpow]; exact he l) M C' hM
  refine ⟨C, fun k n φ h1 h2 h3 h4 => ?_⟩
  have h := hC k n φ h1 h2 h3 h4
  have e : timeVariablesAAlpha C k n (1 / 2) = timeN C k n := by
    unfold timeVariablesAAlpha timeN expN
    rw [← Real.sqrt_eq_rpow]
  rwa [e] at h
end PairsToBound
