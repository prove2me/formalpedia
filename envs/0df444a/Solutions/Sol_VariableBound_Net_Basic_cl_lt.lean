-- Prove2me | solution 1 for VariableBound.Net.Basic.cl_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:01:51.676333+00:00
-- url     : https://prove2.me/submissions/8ed74969-7532-46d8-8a33-b643942bcbd5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Finset.Card
import Definitions.Def_VariableBound_Net_Basic
import Theorems.Thm_VariableBound_Net_Basic_mem_objs
import Theorems.Thm_VariableBound_Net_Basic_obAt_mem
import Theorems.Thm_VariableBound_Net_Basic_getD_mem
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
theorem _root_.solution (hW : WfD k n D) {o : ℕ} (h : o < (objs D).length) : (obAt D o).2.1 < D.1.length := by
  rcases mem_objs.1 (obAt_mem h) with h' | h'
  · exact h'.2.1
  · exact (hW.2 _ (getD_mem h'.2.1)).2 _ h'.2.2
end VariableBound.Net.Basic
