-- Prove2me | solution 1 for Wrap.everyMachineCanBeWrapped_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:11:51.96649+00:00
-- url     : https://prove2.me/submissions/69c3a541-f725-478b-8fd1-ed0190adf26a

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
import Theorems.Thm_Wrap_wraps_of_coding
import Theorems.Thm_Groundwork_PolyT_elim


set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork CircuitLowerBound.Tab
variable {M : TM2ComputableAux Bool Bool}
namespace Wrap
theorem _root_.solution (h : ∀ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) → Nonempty (Coding M)) : EveryMachineCanBeWrapped :=
  fun M hM _ _ hpre hpost => (h M hM).elim fun K => wraps_of_coding K hpre hpost
end Wrap
