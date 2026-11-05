-- Prove2me | solution 1 for Wrap.Conf.length_stay_top_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:12:12.691834+00:00
-- url     : https://prove2.me/submissions/c8e663fa-0e2d-4261-a6cc-ba07867dfc73

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
import Theorems.Thm_CircuitLowerBound_Tab_length_nxt_le
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Wrap Wrap.Conf
open Turing Groundwork CircuitLowerBound.Tab
variable (M : TM2ComputableAux Bool Bool)
namespace Wrap.Conf
theorem _root_.solution (c : M.tm.Cfg) (k : M.tm.K) : ((stay M (top M c)).stk k).length ≤ 2 * dep M := by
  rw [← nxt_caseOf]; exact length_nxt_le M _ k
end Wrap.Conf
