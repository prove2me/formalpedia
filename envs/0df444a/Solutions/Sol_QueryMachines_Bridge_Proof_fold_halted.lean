-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.fold_halted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:53:28.729349+00:00
-- url     : https://prove2.me/submissions/4482320c-aa63-495c-ae86-6fb0a902df14

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_CountedToPadded_Compare
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_CountedToPadded_RunFor
import Theorems.Thm_QueryMachines_Bridge_Proof_cutAt_some
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.PolyT PaddedDescent.F
variable {α β : Type} {N : Stepped α β} [Enc N.σ] [Carried N.σ] {S room : ℕ} {b : β}
namespace QueryMachines.Bridge.Proof
theorem _root_.solution (hS : 7 * S + 2 ≤ room) {s : N.σ} (h1 : N.out s = some b) (h2 : size s ≤ S) (fuel : U) :
    fuel.foldl (fun (s : Option N.σ) _ => cutAt room (s.map (stay N))) (some s) = some s := by
  induction fuel with
  | nil => rfl
  | cons u l ih =>
    have e : stay N s = s := if_pos (by rw [h1]; rfl)
    rw [List.foldl_cons, Option.map_some, e, cutAt_some hS h2, ih]
end QueryMachines.Bridge.Proof
