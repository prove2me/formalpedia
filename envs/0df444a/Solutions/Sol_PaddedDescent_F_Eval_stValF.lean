-- Prove2me | solution 1 for PaddedDescent.F.Eval.stValF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:20.313561+00:00
-- url     : https://prove2.me/submissions/08650eac-8edd-4274-9a9b-c60ced9c6884

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_PaddedDescent_F_Eval
import Theorems.Thm_PaddedDescent_F_Eval_val_core
import Theorems.Thm_PaddedDescent_F_Eval_length_gU
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Eval
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open PaddedDescent.F.Mark (Cl trunc Good nSat occ placeAt placeE layersE Asked MCtx markF markN adm nProf cls WfL)
namespace PaddedDescent.F.Eval
theorem _root_.solution (hR : StR) (hD : StD) : StValF := by
  intro C F c pad S Ub₀ P N hT hN hS hU
  have hg := length_gU S.2
  unfold valF
  refine val_core hR hD F c pad S.1 S.2.length (gU S.2).length Ub₀ P hg N hT.two_le hT.chain ?_ ?_ hT.lab ?_ ?_ hN hS hU
  · rw [hg]; exact hT.col
  · rw [hg]; exact hT.st
  · rw [hg]; exact hT.tab
  · rw [hg]; exact hT.fits
end PaddedDescent.F.Eval
