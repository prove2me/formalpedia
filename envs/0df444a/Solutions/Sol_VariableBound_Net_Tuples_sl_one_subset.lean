-- Prove2me | solution 1 for VariableBound.Net.Tuples.sl_one_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:54:54.273727+00:00
-- url     : https://prove2.me/submissions/2f8b5efe-5a7b-4f63-8eb9-c92994c6c077

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
import Theorems.Thm_VariableBound_Net_Tuples_mem_setD
import Theorems.Thm_VariableBound_Net_Tuples_getD_chks
import Theorems.Thm_VariableBound_Net_Tuples_mem_sl
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
theorem _root_.solution {P : Finset ℕ} (hP : P ⊆ range (objs D).length) (j : ℕ) : sl D 1 j P ⊆ (chks D).getD j ∅ := by
  intro e he
  obtain ⟨o, ho, hx⟩ := mem_sl.1 he
  have h := (inc_mem (mem_range.1 (hP ho)) (by rw [hx])).2
  rw [hx] at h
  rw [getD_chks, mem_setD]
  exact h
end VariableBound.Net.Tuples
