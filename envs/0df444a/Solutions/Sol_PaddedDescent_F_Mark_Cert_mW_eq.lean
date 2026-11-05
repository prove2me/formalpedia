-- Prove2me | solution 1 for PaddedDescent.F.Mark.Cert.mW_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:25:40.385117+00:00
-- url     : https://prove2.me/submissions/b86f3581-547b-4f16-b36d-177870035907

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_PaddedDescent_F_CertMark

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Cert
open Groundwork Groundwork.Prog Groundwork.Grid
variable {α : Type} [Enc α]
namespace PaddedDescent.F.Mark.Cert
theorem _root_.solution (g n : ℕ) (Ls : List Fml) (y a : ℕ) (z : List Bool) : mW g n Ls y a z =
    if mW1 g n a z && mW2 g n Ls a z && mW3 g n Ls y a z && mW4 g n Ls y a z then (-1) ^ mWs g n Ls a z else 0 := rfl
end PaddedDescent.F.Mark.Cert
