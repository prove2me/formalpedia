-- Prove2me | solution 1 for SingleBitPieces.SecCrossing_PolyA.unary_min_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:23:14.561455+00:00
-- url     : https://prove2.me/submissions/98af3121-b786-4a48-9901-7ac7550190c6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecCrossing_Crossing
import Definitions.Def_PaddedDescent_F_FuelCert
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Log
import Definitions.Def_SingleBitPieces_SecCrossing_PolyA
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_poly


set_option autoImplicit false
section
section
open SingleBitPieces
open Groundwork PaddedDescent.F Finset
open SingleBitPieces.SecCrossing_PolyA
variable {α : Type} [Enc α]
namespace SingleBitPieces.SecCrossing_PolyA
theorem _root_.solution {f g : α → ℕ} (hf : PolyT f) (hg : Unary g) : Unary fun x => min (f x) (g x) :=
  Unary.of_le hg (PolyT.min' hf hg.poly) fun _ => min_le_right _ _
end SingleBitPieces.SecCrossing_PolyA
