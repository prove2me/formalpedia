-- Prove2me | solution 1 for PaddedDescent.F.Mark.Deg.length_filter_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:53:09.646182+00:00
-- url     : https://prove2.me/submissions/50340ac5-db8e-440e-a2ee-b60b749dd0bf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_PaddedDescent_F_MarkDeg
import Theorems.Thm_PaddedDescent_F_Mark_Deg_map_getD_range
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Deg
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify
open WidthK (theta bsum leafC lay)
open WidthK.Prog (stepK NF toFin)
namespace PaddedDescent.F.Mark.Deg
theorem _root_.solution {α : Type*} (l : List α) (d : α) (p : α → Bool) :
    ((List.range l.length).filter fun e => p (l.getD e d)).length = l.countP p := by
  conv_rhs => rw [← map_getD_range l d, List.countP_map]
  rw [List.countP_eq_length_filter]
  rfl
end PaddedDescent.F.Mark.Deg
