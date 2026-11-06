-- Prove2me | solution 1 for SizeCircuit.stSizedFromEngines
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:30:41.574473+00:00
-- url     : https://prove2.me/submissions/f5473e70-8b62-4682-99d4-0ddc3d369662

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_SizeCircuit_Circuit
import Definitions.Def_SizeCircuit_Cert
import Definitions.Def_SizeCircuit_Sized
import Definitions.Def_SizeCircuit_SizedCert
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Main
import Theorems.Thm_SizeCircuit_stSizedBy
import Theorems.Thm_SizeCircuit_stSizedCert


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound Eight
namespace SizeCircuit
theorem _root_.solution : StSizedFromEngines := by
  intro En hEn gates a hT hC w δ hδ
  have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hd : 0 < δ / ((a : ℝ) + 1) := div_pos hδ ha
  have hle : δ / ((a : ℝ) + 1) * ((a : ℝ) + 1) ≤ δ := le_of_eq (div_mul_cancel₀ δ ha.ne')
  obtain ⟨ℓ, τ, hP, c, hc⟩ := hEn (max w 3) (le_max_of_le_right (by norm_num)) (δ / ((a : ℝ) + 1)) hd
  exact ⟨ℓ, τ, stSizedCert gates hC _ hP, stSizedBy gates a hT w δ _ hδ hd.le hle _ c hc⟩
end SizeCircuit
