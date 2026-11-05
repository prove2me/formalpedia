-- Prove2me | solution 1 for Wrap.Conf.ks_outIdx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:02:02.077926+00:00
-- url     : https://prove2.me/submissions/6a868105-295a-4e09-84e6-1b10a004f10c

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

set_option autoImplicit false
section
section
open Wrap Wrap.Conf
open Turing Groundwork CircuitLowerBound.Tab
variable (M : TM2ComputableAux Bool Bool)
variable [∀ i, Finite (M.tm.Γ i)]
omit [∀ i, Finite (M.tm.Γ i)]
namespace Wrap.Conf
theorem _root_.solution : (ks M)[outIdx M]? = some M.tm.k₁ := (List.mem_iff_getElem?.1 (mem_ks M M.tm.k₁)).choose_spec
end Wrap.Conf
