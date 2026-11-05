-- Prove2me | solution 1 for P2M_Groundwork_PolyT_inl__78f4b62d65a1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:55:07.315749+00:00
-- url     : https://prove2.me/submissions/0c7c4331-0dc7-4e95-8576-286f48bfe86f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Closure_Basic
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_of_wd

attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.prodMk

set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Enc
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
namespace Groundwork.PolyT
theorem _root_.solution {f : α → β} (hf : PolyT f) : PolyT (fun x => (Sum.inl (f x) : β ⊕ γ)) :=
  of_wd (prodMk (const false) hf) id (fun _ => rfl) fun _ => rfl
end Groundwork.PolyT
