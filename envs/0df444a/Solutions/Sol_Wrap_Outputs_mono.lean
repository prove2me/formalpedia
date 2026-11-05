-- Prove2me | solution 1 for Wrap.Outputs.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:44:10.779805+00:00
-- url     : https://prove2.me/submissions/769299dc-33c9-4b74-8103-ef98536b51fa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Coding
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_CountKSat_Host
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_Wrap_Sim
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork CircuitLowerBound.Tab
variable {M : TM2ComputableAux Bool Bool}
namespace Wrap
namespace Outputs
theorem _root_.solution {N : TM2ComputableAux Bool Bool} {x y : List Bool} {t t' : ℕ} (h : Outputs N x y t) (ht : t ≤ t') : Outputs N x y t' := by
  obtain ⟨ev⟩ := h
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ht⟩⟩
end Outputs
end Wrap
