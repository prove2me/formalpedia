-- Prove2me | solution 1 for SizeCircuit.stSizedFromEngine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:30:40.013901+00:00
-- url     : https://prove2.me/submissions/c4007d12-3411-4b86-b186-1022a2223d60

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
theorem _root_.solution : StSizedFromEngine := by
  intro hEng gates a hT hC w δ hδ
  have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hd : 0 < δ / ((a : ℝ) + 1) := div_pos hδ ha
  have hle : δ / ((a : ℝ) + 1) * ((a : ℝ) + 1) ≤ δ := le_of_eq (div_mul_cancel₀ δ ha.ne')
  obtain ⟨E, hE, c, hc⟩ := hEng (max w 3) (le_max_of_le_right (by norm_num)) (δ / ((a : ℝ) + 1)) hd
  exact ⟨E, _, c, hE, hd.le, hle, hc, stSizedCert gates hC E hE, stSizedBy gates a hT w δ _ hδ hd.le hle E c hc⟩
end SizeCircuit
