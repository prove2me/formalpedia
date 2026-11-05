-- Prove2me | solution 1 for PaddedDescent.sOf_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:04:53.435734+00:00
-- url     : https://prove2.me/submissions/1596f1e1-65c6-4b43-ab20-c5ad7eb1e7be

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_PadRate
import Definitions.Def_PaddedDescent_BrutePad
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_PaddedDescent_Reduce
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_P2M_Groundwork_PolyT_log2__935ea318e2e8
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.div
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] P2M_Groundwork_PolyT_log2__935ea318e2e8



set_option autoImplicit false
section
open PaddedDescent
open Groundwork Groundwork.Decode Sat3 Turing
namespace PaddedDescent
theorem _root_.solution {α : Type} [Enc α] {f : α → ℕ} (hf : PolyT f) : PolyT fun x => sOf (f x) :=
  PolyT.div (PolyT.mul (PolyT.const 3) (PolyT.sub (PolyT.log2' (PolyT.log2' hf)) (PolyT.const 911))) (PolyT.const 19)
end PaddedDescent
