-- Prove2me | solution 1 for PaddedDescent.F.CertSide.boolCases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:42:12.873082+00:00
-- url     : https://prove2.me/submissions/f51f7408-bd9f-411a-b02a-0b2a2c6c0376

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_GridSide
import Definitions.Def_PaddedDescent_F_CertSide
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertSide
open Groundwork Groundwork.Prog Groundwork.Grid
variable {α : Type} [Enc α]
namespace PaddedDescent.F.CertSide
theorem _root_.solution {β : Type} [Enc β] {F : Bool → α → β} (h : ∀ b, PolyT (F b)) {tr : α → Bool} (ht : PolyT tr) :
    PolyT fun x => F (tr x) x :=
  (PolyT.cond' ht (h true) (h false)).congr fun x => by cases tr x <;> rfl
end PaddedDescent.F.CertSide
