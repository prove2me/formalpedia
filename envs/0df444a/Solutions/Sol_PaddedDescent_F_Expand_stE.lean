-- Prove2me | solution 1 for PaddedDescent.F.Expand.stE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:55:14.672288+00:00
-- url     : https://prove2.me/submissions/d1448b74-88b6-4281-98fd-f3177afe3481

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_SideF
import Definitions.Def_PaddedDescent_F_Expand
import Theorems.Thm_PaddedDescent_F_Expand_sum_map_range
import Theorems.Thm_PaddedDescent_F_Expand_filterMap_spec
import Theorems.Thm_Groundwork_BitCut_expand
import Theorems.Thm_Groundwork_Grid_ZW_eq_sum
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Stepped_sum_map_range
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_SideF_stChild
import Theorems.Thm_PaddedDescent_F_rng_eq
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Expand
open Groundwork Groundwork.Prog Groundwork.Grid Finset
namespace PaddedDescent.F.Expand
theorem _root_.solution : StE := by
  intro pad L Λ B I hK hg hI hb
  have hpat : (I.1.length + 1) ^ nRect L.2.length ≤ (Λ + 1) ^ nRect L.2.length :=
    Nat.pow_le_pow_left (Nat.succ_le_succ hI.lam_le) _
  obtain ⟨h1, h2, h3⟩ := filterMap_spec (f := childF pad L I) (z := zval L.1.length)
    (v := sideZ L.2.length I.1.length (instOf (K := L.2.length * L.2.length) I.2))
    (Q := WF L.1.length (lamNext L.1.length L.2.length Λ) (bNext L.1.length L.2.length Λ B))
    (List.range ((I.1.length + 1) ^ nRect L.2.length))
    fun y hy => SideF.stChild pad L Λ B I y hK hg hI hb (List.mem_range.1 hy)
  unfold expand
  rw [rng_eq (hpat.trans hb.pat)]
  refine ⟨?_, h2, by rw [h3, List.length_range]; exact hpat⟩
  rw [h1, sum_map_range, zval, ZW_eq_sum]
end PaddedDescent.F.Expand
