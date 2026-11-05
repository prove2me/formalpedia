-- Prove2me | solution 1 for WidthK.Refine.length_overP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:21:22.46609+00:00
-- url     : https://prove2.me/submissions/34f289d9-d24f-4264-9d64-2080db3ae3f6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_WidthK_Refine_card_toFin
import Theorems.Thm_WidthK_Refine_NF_filter
import Theorems.Thm_WidthK_Refine_toFin_overP
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
namespace WidthK.Refine
theorem _root_.solution {s : PFml} (hs : NF s) (j : ℕ) (H : PCl) :
    (overP s j H).length = (Sparsify.over (toFin s) j H.toFinset).card := by
  rw [← toFin_overP hs.1, overP, card_toFin (NF_filter hs _)]
end WidthK.Refine
