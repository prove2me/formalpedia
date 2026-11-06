-- Prove2me | solution 1 for P2M_ExplicitCost_length_unary__ce48a98cee10
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:52:05.547507+00:00
-- url     : https://prove2.me/submissions/ab891457-6514-403e-9d13-45bb37b13d06

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_AnswersDefs
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Numbers
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (n : ℕ) : (unary n).length = n := List.length_replicate
end ExplicitCost
