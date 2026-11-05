-- Prove2me | solution 1 for P2M_Groundwork_PolyT_table__fffc2d45394e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:35:25.088925+00:00
-- url     : https://prove2.me/submissions/8624dffb-262b-4a1f-8da5-cd13decde689

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Bool
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Definitions.Def_ToTuring_Lib_Table
import Theorems.Thm_P2M_Groundwork_PolyT_table__41b4aef3a617
import Theorems.Thm_Groundwork_PolyT_prodMk
attribute [local fun_prop] Groundwork.PolyT.prodMk



set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε ζ : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε] [Enc ζ]
namespace Groundwork.PolyT
theorem _root_.solution [Finite β] [DecidableEq β] [EqT β] [Finite γ] [DecidableEq γ] [EqT γ] (F : β → γ → ζ) {f : α → β} {g : α → γ}
    (hf : PolyT f) (hg : PolyT g) : PolyT fun x => F (f x) (g x) :=
  table₁ (fun t : β × γ => F t.1 t.2) (prodMk hf hg)
end Groundwork.PolyT
