-- Prove2me | solution 1 for Wrap.Conf.size_var_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:10:54.310887+00:00
-- url     : https://prove2.me/submissions/2d7d0848-3144-4e17-96ad-e228064a8646

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
theorem _root_.solution (v : M.tm.σ) : size (num v) ≤ bnd M := size_nat_le (by have := num_lt v; omega)
end Wrap.Conf
