-- Prove2me | solution 1 for VariableBound.Net.Tuples.back_sl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:49:44.080207+00:00
-- url     : https://prove2.me/submissions/307cbadf-2888-4f3e-883f-2198264f100d

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
import Theorems.Thm_VariableBound_Net_Tuples_mem_sl
import Theorems.Thm_VariableBound_Net_Tuples_mem_back
import Theorems.Thm_VariableBound_Net_Tuples_third_zero
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_Net_Basic_cl_lt
import Theorems.Thm_VariableBound_Net_Basic_inc_mem
import Theorems.Thm_VariableBound_Net_Basic_kind_cases
import Theorems.Thm_VariableBound_Net_Basic_obAt_inj
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Tuples
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
open ClauseBound.ParityChecks (Vof)
variable {k n : ℕ} {D : Dat}
namespace VariableBound.Net.Tuples
theorem _root_.solution (hW : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) :
    back D (sl D 0 0 P) (fun j : Fin (chks D).length => sl D 1 j.val P) = P := by
  ext o
  rw [mem_back]
  constructor
  · rintro ⟨ho, ⟨e, he, hx⟩ | ⟨j, e, he, hx⟩⟩
    · obtain ⟨o', ho', hx'⟩ := mem_sl.1 he
      rwa [obAt_inj hW ho (mem_range.1 (hP ho')) (hx.trans hx'.symm)]
    · obtain ⟨o', ho', hx'⟩ := mem_sl.1 he
      rwa [obAt_inj hW ho (mem_range.1 (hP ho')) (hx.trans hx'.symm)]
  · intro hoP
    have ho := mem_range.1 (hP hoP)
    refine ⟨ho, ?_⟩
    rcases kind_cases ho with h0 | h1
    · have hx : obAt D o = (0, (obAt D o).2.1, 0) := Prod.ext h0 (Prod.ext rfl (third_zero ho h0))
      exact Or.inl ⟨⟨(obAt D o).2.1, cl_lt hW ho⟩, mem_sl.2 ⟨o, hoP, hx⟩, hx⟩
    · have hx : obAt D o = (1, (obAt D o).2.1, (obAt D o).2.2) := Prod.ext h1 rfl
      exact Or.inr ⟨⟨(obAt D o).2.2, by rw [length_chks]; exact (inc_mem ho h1).1⟩, ⟨(obAt D o).2.1, cl_lt hW ho⟩, mem_sl.2 ⟨o, hoP, hx⟩, hx⟩
end VariableBound.Net.Tuples
