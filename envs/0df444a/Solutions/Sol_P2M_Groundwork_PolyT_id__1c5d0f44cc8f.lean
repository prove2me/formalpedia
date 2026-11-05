-- Prove2me | solution 1 for P2M_Groundwork_PolyT_id__1c5d0f44cc8f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:46:50.406426+00:00
-- url     : https://prove2.me/submissions/31a8e128-bad5-469b-aa4c-a1692eb36da6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Closure_Basic
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_of
import Theorems.Thm_Groundwork_TM_pushW_within
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4


set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Enc
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
namespace Groundwork.PolyT
theorem _root_.solution : PolyT (fun x : α => x) :=
  PolyT.of (pushW []) (PB.const 1) PB.id' (fun x M A B N => pushW_within (wd x ++ M) A B N []) fun _ => le_rfl
end Groundwork.PolyT
