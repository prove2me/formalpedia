-- Prove2me | solution 1 for Wrap.Conf.polyT_map_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:11:05.834807+00:00
-- url     : https://prove2.me/submissions/d32c5d9d-9d1b-46da-8384-5236a79b8372

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
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86



set_option autoImplicit false
section
section
open Wrap Wrap.Conf
open Turing Groundwork CircuitLowerBound.Tab
namespace Wrap.Conf
theorem _root_.solution {ι α β : Type} [Enc α] [Enc β] (l : List ι) (g : ι → α → β) (h : ∀ i, PolyT (g i)) :
    PolyT fun x => l.map fun i => g i x := by
  induction l with
  | nil => exact PolyT.const []
  | cons i l ih => exact PolyT.cons' (h i) ih
end Wrap.Conf
