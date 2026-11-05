-- Prove2me | solution 1 for Wrap.run_sim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:57:08.459027+00:00
-- url     : https://prove2.me/submissions/868d7772-ce54-4efb-9062-a3285dc4b488

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
import Theorems.Thm_Wrap_next_sim
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork CircuitLowerBound.Tab
variable {M : TM2ComputableAux Bool Bool}
namespace Wrap
theorem _root_.solution (K : Coding M) (pre post : List Bool → List Bool) (x : List Bool) (j : ℕ) :
    (sim K pre post).run x j = K.rep ((stay M)^[j] (initList M.tm ((pre x).map M.inputAlphabet.invFun))) := by
  induction j with
  | zero => exact K.init_rep (pre x)
  | succ j ih =>
    rw [Function.iterate_succ_apply', ← next_sim K pre post, ← ih]
    exact Function.iterate_succ_apply' _ _ _
end Wrap
