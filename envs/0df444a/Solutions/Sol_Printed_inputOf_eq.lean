-- Prove2me | solution 1 for Printed.inputOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:17:30.317345+00:00
-- url     : https://prove2.me/submissions/41f80085-d237-4034-9f2d-ef81cf209f2a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingProcs
import Theorems.Thm_Printed_map_range_eq_ofFn
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Prog_map_range_eq_ofFn
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight Eight.SecNetworks QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution {g : ℕ} (N : Net g) (P B : ℕ) (len : ℕ → ℕ) (cap : ℕ → ℕ → ℕ) (hl : ∀ a : Fin g, len a = N.len a) (hc : ∀ a b : Fin g, a ≠ b → cap a b = N.c a b) :
    inputOf g P B len cap = netInput N P B := by
  unfold inputOf netInput
  rw [map_range_eq_ofFn (fun a => unary (len a)) (fun a : Fin g => unary (N.len a)) fun a => by rw [hl],
    map_range_eq_ofFn (fun a => (List.range g).map fun b => if a = b then [] else unary (cap a b)) (fun a : Fin g => List.ofFn fun b : Fin g => if a = b then [] else unary (N.c a b)) fun a =>
      map_range_eq_ofFn _ _ fun b => by
        by_cases hab : a = b
        · rw [if_pos hab, if_pos (congrArg Fin.val hab)]
        · rw [if_neg hab, if_neg fun e => hab (Fin.ext e), hc a b hab]]
end Printed
