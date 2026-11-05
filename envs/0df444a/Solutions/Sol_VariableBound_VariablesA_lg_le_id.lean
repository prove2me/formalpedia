-- Prove2me | solution 1 for VariableBound.VariablesA.lg_le_id
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:16:09.540382+00:00
-- url     : https://prove2.me/submissions/fca886ff-2c13-4c14-88b1-718c208a433c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Printed_VariablesA_Setting

set_option autoImplicit false
section
section
open VariableBound VariableBound.VariablesA
open MainTheoremForms
namespace VariableBound.VariablesA
theorem _root_.solution {t : ℝ} (ht : 0 < t) : MainTheoremForms.lg t ≤ t := by
  have h1 : Real.log (t / 2) ≤ t / 2 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div ht.ne' (by norm_num)] at h1
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_two_lt_d9
  rw [MainTheoremForms.lg, Real.logb, div_le_iff₀ (by linarith)]
  nlinarith
end VariableBound.VariablesA
