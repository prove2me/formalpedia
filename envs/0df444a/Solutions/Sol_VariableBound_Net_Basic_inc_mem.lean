-- Prove2me | solution 1 for VariableBound.Net.Basic.inc_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:01:41.057443+00:00
-- url     : https://prove2.me/submissions/19187b46-9cf6-4f92-a174-87758f3eaec1

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
theorem _root_.solution {o : ℕ} (h : o < (objs D).length) (h1 : (obAt D o).1 = 1) :
    (obAt D o).2.2 < D.2.length ∧ (obAt D o).2.1 ∈ D.2.getD (obAt D o).2.2 [] := by
  rcases mem_objs.1 (obAt_mem h) with h' | h'
  · omega
  · exact h'.2
end VariableBound.Net.Basic
