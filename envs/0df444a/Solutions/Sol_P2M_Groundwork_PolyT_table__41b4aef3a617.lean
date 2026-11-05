-- Prove2me | solution 1 for P2M_Groundwork_PolyT_table__41b4aef3a617
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:24:37.568264+00:00
-- url     : https://prove2.me/submissions/3751cdeb-85f5-4d47-85d2-332cce527ad5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Bool
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Definitions.Def_ToTuring_Lib_Table
import Theorems.Thm_Groundwork_PolyT_table
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
attribute [local fun_prop] Groundwork.PolyT.comp



set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε ζ : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε] [Enc ζ]
namespace Groundwork.PolyT
theorem _root_.solution [Finite β] [DecidableEq β] [EqT β] (F : β → ζ) {f : α → β} (hf : PolyT f) : PolyT fun x => F (f x) :=
  comp (table F) hf
end Groundwork.PolyT
