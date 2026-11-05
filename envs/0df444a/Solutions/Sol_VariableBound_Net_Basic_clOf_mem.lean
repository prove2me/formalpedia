-- Prove2me | solution 1 for VariableBound.Net.Basic.clOf_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:40:39.80544+00:00
-- url     : https://prove2.me/submissions/ceb13eb3-0b8b-495b-88b8-84c19a4ffb23

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Finset.Card
import Definitions.Def_VariableBound_Net_Basic
import Theorems.Thm_VariableBound_Net_Basic_cl_lt
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Basic
open Groundwork Groundwork.Prog PaddedDescent.F
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
variable {k g n : ℕ} {D : Dat}
namespace VariableBound.Net.Basic
theorem _root_.solution (hW : WfD k n D) {o : ℕ} (h : o < (objs D).length) : clOf D o ∈ D.1 := by
  rw [clOf, List.getD_eq_getElem _ _ (cl_lt hW h)]; exact List.getElem_mem _
end VariableBound.Net.Basic
