-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.len_cutAt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:53:36.995566+00:00
-- url     : https://prove2.me/submissions/cf8ced0d-b647-4296-8b9e-27d97e999547

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
namespace QueryMachines.Bridge.Proof
theorem _root_.solution {γ : Type} [Enc γ] (room : ℕ) (x : Option γ) : len (cutAt room x) ≤ room + 2 := by
  unfold cutAt
  split
  · omega
  · rw [len_none]; omega
end QueryMachines.Bridge.Proof
