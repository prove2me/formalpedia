-- Prove2me | solution 1 for Paper.Achievable.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:56:39.468702+00:00
-- url     : https://prove2.me/submissions/a7bb5cc6-09af-4f05-bc25-acc4b0c3249a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecNetworks_Model
import Definitions.Def_StepMachines_Prog_BruteE
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Math_RebalanceArith
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Poly_Brute
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_Paper_SecNetworks_Networks
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Paper
open Groundwork Groundwork.Prog Finset
namespace Paper
namespace Achievable
theorem _root_.solution {K : ℕ} {e e₁ : ℝ} (h : Achievable K e) (he : e ≤ e₁) : Achievable K e₁ :=
  let ⟨E, hk, hc⟩ := h
  ⟨E, hk, hc.mono he⟩
end Achievable
end Paper
