-- Prove2me | solution 1 for ThmCount.frontEnd_enc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:06:27.39707+00:00
-- url     : https://prove2.me/submissions/654bebcc-bd8c-422e-82d7-505bf50b5cae

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_Wrap_FrontEnd
import Definitions.Def_WidthK_Decode
import Definitions.Def_ToTuring_Poly_Decode
import Mathlib.Tactic
import Definitions.Def_ThmCount_FrontEnd
import Theorems.Thm_ThmCount_encPlain_toN
import Theorems.Thm_Groundwork_Decode_dec_enc
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_takeWhile
import Theorems.Thm_Wrap_toN_pad4
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.takeWhile



set_option autoImplicit false
section
section
section
open ThmCount
open Groundwork Groundwork.Decode
namespace ThmCount
theorem _root_.solution {n : ℕ} {φ : Sat3.CNF n} (hφ : ∀ C ∈ φ, C.length ≤ 3) : frontEnd (Sat3.enc φ) = SatM.enc 3 (Wrap.pad4 φ) := by
  have h1 : ((Sat3.enc φ).takeWhile id).length = n := congrArg Prod.fst (dec_enc hφ)
  rw [frontEnd, Wrap.slotBits, h1, dec_enc hφ, ← Wrap.toN_pad4, encPlain_toN]
end ThmCount
