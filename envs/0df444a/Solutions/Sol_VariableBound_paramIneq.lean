-- Prove2me | solution 1 for VariableBound.paramIneq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:59:59.278699+00:00
-- url     : https://prove2.me/submissions/8367625c-334f-454a-98cb-df57915f0029

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Ineq
import Theorems.Thm_VariableBound_Ineq_m_div_lt
import Theorems.Thm_VariableBound_Ineq_three_m_lt
import Theorems.Thm_VariableBound_Ineq_six_le
import Theorems.Thm_P2M_VariableBound_Ineq_beta_le__a4c5e212e2ce
import Theorems.Thm_P2M_VariableBound_Ineq_beta_le__a4eb7ef2dfed
import Theorems.Thm_VariableBound_Ineq_rb_le
import Theorems.Thm_VariableBound_Ineq_large
import Theorems.Thm_VariableBound_Ineq_p_rb
import Theorems.Thm_VariableBound_Ineq_tb_le

set_option autoImplicit false
section
section
open VariableBound
open AppVariables
namespace VariableBound
theorem _root_.solution : ParamIneq where
  sb_lt n Δ m nb hΔ hm h := by
    have h1 := Ineq.m_div_lt hΔ hm h
    refine ⟨h1, ?_⟩
    rw [mul_div_assoc]
    linarith
  three_m n Δ m nb hΔ hm h := ⟨Ineq.three_m_lt hΔ hm h, Ineq.six_le hΔ⟩
  beta_le n Δ m nb hΔ hnm hm h := ⟨Ineq.beta_le₁ hΔ hnm hm h, Ineq.beta_le₂ (by omega) h⟩
  rb_le β rb h := Ineq.rb_le h
  large n Δ m nb rb hΔ hnm hm h hr hn := Ineq.large hΔ hnm hm h hr hn
  p_rb n Δ nb rb hΔ h hr := Ineq.p_rb hΔ h hr
  tb_le n Δ m nb rb tb hΔ hm h hr ht := Ineq.tb_le hΔ hm h hr ht
end VariableBound
