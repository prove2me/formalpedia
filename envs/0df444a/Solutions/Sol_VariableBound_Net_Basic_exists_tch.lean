-- Prove2me | solution 1 for VariableBound.Net.Basic.exists_tch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:54:15.224551+00:00
-- url     : https://prove2.me/submissions/bf9b1270-210a-4704-96d8-04313655d8f4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Finset.Card
import Definitions.Def_VariableBound_Net_Basic
import Theorems.Thm_VariableBound_Net_Basic_clOf_wf
import Theorems.Thm_VariableBound_Net_Basic_tchB_iff
import Theorems.Thm_VariableBound_Net_Basic_div_qv_lt
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
theorem _root_.solution (hg : 0 < g) (hW : WfD k n D) {o : ℕ} (ho : o < (objs D).length) : ∃ a < g, tchB g n D a o = true := by
  obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ (clOf_wf hW ho).1
  exact ⟨l.1 / qv g n, div_qv_lt hg ((clOf_wf hW ho).2.2 l hl), tchB_iff.2 (Or.inl ⟨l, hl, rfl⟩)⟩
end VariableBound.Net.Basic
