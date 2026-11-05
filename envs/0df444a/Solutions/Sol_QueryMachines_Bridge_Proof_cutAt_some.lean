-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.cutAt_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:02:08.147937+00:00
-- url     : https://prove2.me/submissions/50a5bc64-c899-4237-8e12-5c4a70c4c825

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_CountedToPadded_Compare
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_CountedToPadded_RunFor

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.PolyT PaddedDescent.F
variable {α β : Type} {N : Stepped α β} [Enc N.σ] [Carried N.σ] {S room : ℕ} {b : β}
namespace QueryMachines.Bridge.Proof
theorem _root_.solution (hS : 7 * S + 2 ≤ room) {s : N.σ} (h : size s ≤ S) : cutAt room (some s) = some s := by
  have := Carried.le s
  exact if_pos (by rw [len_some]; omega)
end QueryMachines.Bridge.Proof
