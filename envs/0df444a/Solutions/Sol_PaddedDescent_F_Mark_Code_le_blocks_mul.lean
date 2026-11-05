-- Prove2me | solution 1 for PaddedDescent.F.Mark.Code.le_blocks_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:59:16.356255+00:00
-- url     : https://prove2.me/submissions/2f9b212c-3a7c-4f83-873c-35d7e4c947f5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_PaddedDescent_F_MarkCode
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Code
open Groundwork
namespace PaddedDescent.F.Mark.Code
theorem _root_.solution {b : ℕ} (h0 : 0 < b) (t : ℕ) : t ≤ (t + b - 1) / b * b := by
  have h3 := Nat.mod_lt (t + b - 1) h0
  have h4 := Nat.div_add_mod (t + b - 1) b
  rw [Nat.mul_comm] at h4
  omega
end PaddedDescent.F.Mark.Code
