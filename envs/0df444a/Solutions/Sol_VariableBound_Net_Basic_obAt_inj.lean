-- Prove2me | solution 1 for VariableBound.Net.Basic.obAt_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:39:14.70784+00:00
-- url     : https://prove2.me/submissions/496eb3dd-6dcf-4856-bcb5-fccbfef412a4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Finset.Card
import Definitions.Def_VariableBound_Net_Basic
import Theorems.Thm_VariableBound_Net_Basic_obAt_eq
import Theorems.Thm_VariableBound_Net_Basic_nodup_objs
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
theorem _root_.solution (hW : WfD k n D) {o o' : ℕ} (h : o < (objs D).length) (h' : o' < (objs D).length) (he : obAt D o = obAt D o') : o = o' := by
  rw [obAt_eq h, obAt_eq h'] at he
  exact (List.Nodup.getElem_inj_iff (nodup_objs hW)).1 he
end VariableBound.Net.Basic
