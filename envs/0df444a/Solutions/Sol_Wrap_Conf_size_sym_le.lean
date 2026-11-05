-- Prove2me | solution 1 for Wrap.Conf.size_sym_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:57:08.380597+00:00
-- url     : https://prove2.me/submissions/47f8d58d-49fc-4b1c-a6fe-6e8fb963ba84

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
namespace Wrap.Conf
theorem _root_.solution (k : M.tm.K) (x : M.tm.Γ k) : size (sym M k x) ≤ bnd M :=
  size_nat_le (by have := num_lt (⟨k, x⟩ : Σ k, M.tm.Γ k); unfold sym; omega)
end Wrap.Conf
