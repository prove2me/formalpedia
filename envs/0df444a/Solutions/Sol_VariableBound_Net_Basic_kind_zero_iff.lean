-- Prove2me | solution 1 for VariableBound.Net.Basic.kind_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:48:43.440991+00:00
-- url     : https://prove2.me/submissions/5772cc17-24ef-4d20-904f-3d6e015668e3

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
import Theorems.Thm_VariableBound_Net_Basic_obAt_inj
import Theorems.Thm_VariableBound_Net_Basic_length_objs
import Theorems.Thm_VariableBound_Net_Basic_obAt_of_lt
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
theorem _root_.solution (hW : WfD k n D) {o : ℕ} (h : o < (objs D).length) : (obAt D o).1 = 0 ↔ o < D.1.length := by
  constructor
  · intro h0
    rcases mem_objs.1 (obAt_mem h) with h' | h'
    · have h2 : obAt D o = obAt D (obAt D o).2.1 := by
        rw [obAt_of_lt h'.2.1]; exact Prod.ext h'.1 (Prod.ext rfl h'.2.2)
      have h3 := obAt_inj hW h (by rw [length_objs]; omega) h2
      omega
    · omega
  · intro h0; rw [obAt_of_lt h0]
end VariableBound.Net.Basic
