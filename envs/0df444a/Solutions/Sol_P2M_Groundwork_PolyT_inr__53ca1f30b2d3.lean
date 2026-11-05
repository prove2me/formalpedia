-- Prove2me | solution 1 for P2M_Groundwork_PolyT_inr__53ca1f30b2d3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:55:08.520774+00:00
-- url     : https://prove2.me/submissions/9eb01d5c-c136-4dd4-85f3-e1ba38db9d4f

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
theorem _root_.solution {f : α → γ} (hf : PolyT f) : PolyT (fun x => (Sum.inr (f x) : β ⊕ γ)) :=
  of_wd (prodMk (const true) hf) id (fun _ => rfl) fun _ => rfl
end Groundwork.PolyT
