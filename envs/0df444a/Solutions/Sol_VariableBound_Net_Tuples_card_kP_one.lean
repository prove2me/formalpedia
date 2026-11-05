-- Prove2me | solution 1 for VariableBound.Net.Tuples.card_kP_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:53:45.467283+00:00
-- url     : https://prove2.me/submissions/81b78973-8f8c-4524-bc8f-ca3edeff32c3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Basic
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
import Definitions.Def_VariableBound_Net_Tuples
import Theorems.Thm_VariableBound_Net_Tuples_length_chks
import Theorems.Thm_VariableBound_Net_Tuples_card_sl
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_VariableBound_Net_Basic_inc_mem
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Tuples
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
open ClauseBound.ParityChecks (Vof)
variable {k n : ℕ} {D : Dat}
namespace VariableBound.Net.Tuples
theorem _root_.solution (hW : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) : #(kP D P 1) = ∑ j : Fin (chks D).length, #(sl D 1 j.val P) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => #(sl D 1 j P)), length_chks,
    Finset.card_eq_sum_card_fiberwise (f := fun o => (obAt D o).2.2) (t := range D.2.length)]
  · refine sum_congr rfl fun j _ => ?_
    rw [card_sl hW hP, kP, filter_filter]
  · intro o ho
    obtain ⟨h1, h2⟩ := mem_filter.1 ho
    exact mem_coe.2 (mem_range.2 (inc_mem (mem_range.1 (hP h1)) h2).1)
end VariableBound.Net.Tuples
