-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.reaches_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:40:31.138104+00:00
-- url     : https://prove2.me/submissions/54cd2abe-5623-4874-9753-26ae0a47c0ee

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
omit [Enc N.σ] [Carried N.σ]
namespace QueryMachines.Bridge.Proof
theorem _root_.solution {s : N.σ} {t : ℕ} (h : N.Reaches S b s t) : size s ≤ S := by
  cases h with
  | halt _ h => exact h
  | step _ h _ => exact h
end QueryMachines.Bridge.Proof
