-- Prove2me | solution 1 for VariableBound.Net.Val.mem_tch_of_mem_tst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:35:42.043226+00:00
-- url     : https://prove2.me/submissions/669078fd-fcc0-4f55-9bc0-f709851f8e23

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_StepMachines_Math_SatNet
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup
import Definitions.Def_VariableBound_Net_Val
import Theorems.Thm_VariableBound_Net_Val_mem_tch
import Theorems.Thm_VariableBound_Net_Val_linkB_iff
import Theorems.Thm_VariableBound_Net_Val_mem_tst
import Theorems.Thm_Groundwork_Prog_Count_linkB_iff
import Theorems.Thm_PaddedDescent_F_Mark_Prof_linkB_iff
import Theorems.Thm_PaddedDescent_F_Mark_Prof_mem_tst


set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL ext)
variable {k g n : ℕ} {D : Dat} {y : ℕ} {fl : Bool}
namespace VariableBound.Net.Val
theorem _root_.solution {a b i e : ℕ} (h : e ∈ tst g n D a b i) : e ∈ tch g n D a := by
  obtain ⟨h1, _, h3⟩ := mem_tst.1 h
  obtain ⟨_, h5, h6, _⟩ := linkB_iff.1 h3
  refine mem_tch.2 ⟨h1, ?_⟩
  rcases le_total a b with hab | hab
  · rwa [min_eq_left hab] at h5
  · rwa [max_eq_left hab] at h6
end VariableBound.Net.Val
