-- Prove2me | solution 1 for P2M_Eight_network_exponent_lt__a4989babe798
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:55:58.784059+00:00
-- url     : https://prove2.me/submissions/2259463c-0c18-4398-8e02-04a0aa2495db

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecProof_NetworkDefs
import Definitions.Def_SingleBitPieces_SecProof_Cost
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_SecProof_Network
import Theorems.Thm_Eight_network_exponent_lt
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper
namespace Eight
theorem _root_.solution {δ' : ℝ} {K U g P m : ℕ} (hδ' : 0 < δ') (h1 : δ' ≤ 1) (hK : 72 / δ' ≤ K) (hU : U < 6 * m) (hP : g * P ≤ 6 * (m + g)) :
    δ' / 12 * ((U : ℝ) + (g : ℝ) * P / K) + 2 * (g : ℝ) * P / K < 3 / 4 * δ' * m + δ' * g := by
  have h := network_exponent_lt hδ' h1 hK hU hP
  have hm : (0 : ℝ) ≤ δ' * m := by positivity
  have hg : (0 : ℝ) ≤ δ' * g := by positivity
  nlinarith
end Eight
