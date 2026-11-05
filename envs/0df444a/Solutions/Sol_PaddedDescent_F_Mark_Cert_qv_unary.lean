-- Prove2me | solution 1 for PaddedDescent.F.Mark.Cert.qv_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:10:54.243704+00:00
-- url     : https://prove2.me/submissions/b8e6ed15-d7e5-45e6-ac3c-726994af8ec7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_PaddedDescent_F_CertMark
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_poly
attribute [local fun_prop] Groundwork.PolyT.const



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Cert
open Groundwork Groundwork.Prog Groundwork.Grid
variable {α : Type} [Enc α]
namespace PaddedDescent.F.Mark.Cert
theorem _root_.solution {g n : α → ℕ} (hg : Unary g) (hn : Unary n) : Unary fun x => qv (g x) (n x) := by
  unfold qv
  exact unary_div (unary_sub (unary_add hn hg) (PolyT.const 1)) hg.poly
end PaddedDescent.F.Mark.Cert
