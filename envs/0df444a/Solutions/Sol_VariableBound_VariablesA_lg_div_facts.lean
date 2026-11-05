-- Prove2me | solution 1 for VariableBound.VariablesA.lg_div_facts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:58:53.466846+00:00
-- url     : https://prove2.me/submissions/024c1c56-832c-49d8-8ca6-6a4b688b7f08

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_ClauseBound_TopN_End
import Definitions.Def_ClauseBound_Alg_End
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Printed_VariablesA_Arith

set_option autoImplicit false
section
section
open VariableBound VariableBound.VariablesA
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.End ClauseBound.TopN ClauseBound.TopN.End MainTheoremForms
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀)
namespace VariableBound.VariablesA
theorem _root_.solution {k : ℕ} {x : ℝ} (hk : 3 ≤ k) (h0 : 0 < x) (h1 : x ≤ 1) : 1 ≤ MainTheoremForms.lg (2 / x) ∧ MainTheoremForms.lg (2 / x) ≤ MainTheoremForms.lg (k / x) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  constructor
  · rw [MainTheoremForms.lg, Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_one, le_div_iff₀ h0]
    linarith
  · exact Real.logb_le_logb_of_le (by norm_num) (by positivity) (div_le_div_of_nonneg_right (by linarith) h0.le)
end VariableBound.VariablesA
