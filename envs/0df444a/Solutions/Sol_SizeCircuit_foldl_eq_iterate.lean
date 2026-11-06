-- Prove2me | solution 1 for SizeCircuit.foldl_eq_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:27:33.193669+00:00
-- url     : https://prove2.me/submissions/e77df78f-9191-4ffb-8a16-e85ec5b074f9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_SizeCircuit_Addition
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_List3
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Cert
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
namespace SizeCircuit
theorem _root_.solution {γ : Type} (f : γ → γ) : ∀ (l : List Unit) (a : γ), l.foldl (fun c _ => f c) a = f^[l.length] a
  | [], _ => rfl
  | _ :: l, a => by rw [List.foldl_cons, solution f l, List.length_cons, Function.iterate_succ_apply]
end SizeCircuit
