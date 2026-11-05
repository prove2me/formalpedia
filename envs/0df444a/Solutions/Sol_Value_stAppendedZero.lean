-- Prove2me | solution 1 for Value.stAppendedZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:54:24.11862+00:00
-- url     : https://prove2.me/submissions/6ab4aa82-4af4-4500-afe4-5fb6467b86c5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_Value_Blocks
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
namespace Value
theorem _root_.solution : StAppendedZero := by
  intro C _ g K Np c N hK0 x Λ h
  obtain ⟨γ, hγ⟩ := not_forall.1 h
  refine Finset.prod_eq_zero (Finset.mem_univ γ) ?_
  unfold display
  rw [if_neg hγ, zero_mul]
end Value
