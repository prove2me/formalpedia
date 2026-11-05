-- Prove2me | solution 1 for PaddedDescent.F.CertGrid.lamNext_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:03.315402+00:00
-- url     : https://prove2.me/submissions/c53cb0ee-e6f7-40e7-a201-486de23a7258

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_PaddedDescent_F_CertGrid
import Theorems.Thm_PaddedDescent_F_CertGrid_lamNext_unary_aux

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertGrid
open Groundwork Groundwork.Prog
variable {α : Type} [Enc α]
namespace PaddedDescent.F.CertGrid
theorem _root_.solution {K g n : α → ℕ} (hK : Unary K) (hg : Unary g) (hn : Unary n) :
    Unary fun x => lamNext (K x) (g x) (n x) := lamNext_unary_aux Dcol hK hg hn
end PaddedDescent.F.CertGrid
