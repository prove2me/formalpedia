-- Prove2me | solution 1 for Wrap.Conf.stay_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:12:54.125421+00:00
-- url     : https://prove2.me/submissions/f14cdd94-3b42-4f7a-85f0-a5d0533284e6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Coding
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Data.Finite.Sigma
import Mathlib.Tactic.Linarith
import Definitions.Def_Wrap_CodingExists
import Theorems.Thm_Wrap_Conf_nxt_caseOf
import Theorems.Thm_CircuitLowerBound_Tab_stay_eq


set_option autoImplicit false
section
section
open Wrap Wrap.Conf
open Turing Groundwork CircuitLowerBound.Tab
variable (M : TM2ComputableAux Bool Bool)
namespace Wrap.Conf
theorem _root_.solution (c : M.tm.Cfg) : stay M c =
    ⟨(stay M (top M c)).l, (stay M (top M c)).var, fun k => (stay M (top M c)).stk k ++ (c.stk k).drop (dep M)⟩ := by
  rw [← nxt_caseOf]; exact stay_eq M c
end Wrap.Conf
