-- Prove2me | solution 1 for PaddedDescent.F.CertSide.boolCasesU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:24:11.452544+00:00
-- url     : https://prove2.me/submissions/7a491409-44c7-4f04-b23f-9f64d7cec2c7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_GridSide
import Definitions.Def_PaddedDescent_F_CertSide
import Theorems.Thm_PaddedDescent_F_CertSide_boolCases

set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertSide
open Groundwork Groundwork.Prog Groundwork.Grid
variable {α : Type} [Enc α]
namespace PaddedDescent.F.CertSide
theorem _root_.solution {F : Bool → α → ℕ} (h : ∀ b, Unary (F b)) {tr : α → Bool} (ht : PolyT tr) : Unary fun x => F (tr x) x :=
  boolCases (F := fun b x => List.replicate (F b x) ()) h ht
end PaddedDescent.F.CertSide
