-- Prove2me | solution 1 for P2M_GeneralPieces_Trim_unary_min__233bb8e7b71f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:07:38.823323+00:00
-- url     : https://prove2.me/submissions/fd613974-c21f-4a7d-a8e7-17e1547e61b6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Trim_Prog
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_GeneralPieces_Trim_Cert
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_poly


set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen
open GeneralPieces.Trim
variable {α : Type} [Enc α] {P : PiecesF}
namespace GeneralPieces.Trim
theorem _root_.solution {f g : α → ℕ} (hf : PolyT f) (hg : Unary g) : Unary fun x => min (f x) (g x) :=
  hg.of_le (PolyT.min' hf hg.poly) fun _ => min_le_right _ _
end GeneralPieces.Trim
