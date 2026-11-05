-- Prove2me | solution 1 for Wrap.Conf.bitOf_sym
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:02:39.538249+00:00
-- url     : https://prove2.me/submissions/005b083d-2e34-4420-a3ed-0a108b000615

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
import Theorems.Thm_Wrap_Conf_sym_injective
import Theorems.Thm_Wrap_Conf_sym_lt
import Theorems.Thm_Groundwork_PolyT_lookup_eq


set_option autoImplicit false
section
section
open Wrap Wrap.Conf
open Turing Groundwork CircuitLowerBound.Tab
variable (M : TM2ComputableAux Bool Bool)
variable [∀ i, Finite (M.tm.Γ i)]
namespace Wrap.Conf
theorem _root_.solution (y : M.tm.Γ M.tm.k₁) : bitOf M (sym M M.tm.k₁ y) = M.outputAlphabet y := by
  have : Nonempty (M.tm.Γ M.tm.k₁) := ⟨y⟩
  rw [bitOf, PolyT.lookup_eq _ _ (List.mem_range.2 (sym_lt M _ y))]
  exact congrArg _ (Function.leftInverse_invFun (sym_injective M _) y)
end Wrap.Conf
