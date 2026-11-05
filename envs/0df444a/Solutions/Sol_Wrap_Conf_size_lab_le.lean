-- Prove2me | solution 1 for Wrap.Conf.size_lab_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:10:44.337209+00:00
-- url     : https://prove2.me/submissions/8bad2071-c2b3-4911-8d0f-68e70a9208a7

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
import Theorems.Thm_Wrap_Conf_num_lt
import Theorems.Thm_Wrap_Conf_size_nat_le

set_option autoImplicit false
section
section
open Wrap Wrap.Conf
open Turing Groundwork CircuitLowerBound.Tab
variable (M : TM2ComputableAux Bool Bool)
variable [∀ i, Finite (M.tm.Γ i)]
omit [∀ i, Finite (M.tm.Γ i)]
namespace Wrap.Conf
theorem _root_.solution (l : Option M.tm.Λ) : size (num l) ≤ bnd M := size_nat_le (by have := num_lt l; omega)
end Wrap.Conf
