-- Prove2me | solution 1 for Wrap.Conf.entry_repOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:00:27.224866+00:00
-- url     : https://prove2.me/submissions/00227bb8-22e6-4050-9e0d-df1ae348df50

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
import Theorems.Thm_Wrap_Conf_repOf_injective

set_option autoImplicit false
section
section
open Wrap Wrap.Conf
open Turing Groundwork CircuitLowerBound.Tab
variable (M : TM2ComputableAux Bool Bool)
variable [∀ i, Finite (M.tm.Γ i)]
namespace Wrap.Conf
theorem _root_.solution (c : M.tm.Cfg) : entry M (repOf M c) = repOf M (stay M c) := by
  rw [entry, Function.leftInverse_invFun (repOf_injective M)]
end Wrap.Conf
