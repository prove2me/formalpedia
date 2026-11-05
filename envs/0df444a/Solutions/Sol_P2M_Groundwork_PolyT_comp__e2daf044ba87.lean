-- Prove2me | solution 1 for P2M_Groundwork_PolyT_comp__e2daf044ba87
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:35:06.846204+00:00
-- url     : https://prove2.me/submissions/df1a7b17-015e-4cae-a3a5-ca69d23c33b1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Bool
import Definitions.Def_ToTuring_Lib_List1
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_prodMk
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.prodMk



set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
namespace Groundwork.PolyT
theorem _root_.solution {f : α → β → γ} {a : δ → α} {b : δ → β} (hf : PolyT fun p : α × β => f p.1 p.2) (ha : PolyT a)
    (hb : PolyT b) : PolyT fun x => f (a x) (b x) :=
  PolyT.comp (f := fun p : α × β => f p.1 p.2) (g := fun x => (a x, b x)) hf (prodMk ha hb)
end Groundwork.PolyT
