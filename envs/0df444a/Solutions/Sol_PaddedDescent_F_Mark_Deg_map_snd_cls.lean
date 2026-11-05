-- Prove2me | solution 1 for PaddedDescent.F.Mark.Deg.map_snd_cls
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:54:57.651205+00:00
-- url     : https://prove2.me/submissions/431db0ae-c0bc-4879-9a55-4f1d3b1d981c

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
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_snd
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.snd



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Deg
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify
open WidthK (theta bsum leafC lay)
open WidthK.Prog (stepK NF toFin)
namespace PaddedDescent.F.Mark.Deg
theorem _root_.solution (Ls : List Fml) : (cls Ls).map Prod.snd = Ls.flatten := by
  conv_rhs => rw [← map_getD_range Ls [], ← List.flatMap_def]
  rw [cls, List.map_flatMap]
  congr 1
  funext i
  rw [List.map_map]
  exact List.map_id _
end PaddedDescent.F.Mark.Deg
