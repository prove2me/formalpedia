-- Prove2me | solution 1 for VariableBound.Net.Val.str_st
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:42:45.221689+00:00
-- url     : https://prove2.me/submissions/39e84647-13f7-45d6-b4cb-eb7ef2608958

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
import Theorems.Thm_VariableBound_Net_Val_mem_tch_of_mem_tst
import Theorems.Thm_VariableBound_Net_Val_mark_st
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL ext)
variable {k g n : ℕ} {D : Dat} {y : ℕ} {fl : Bool}
namespace VariableBound.Net.Val
theorem _root_.solution (σ : ℕ → Bool) (P : Finset ℕ) (a a' i : ℕ) :
    str g n D a a' i (st g n D σ P a) = (tst g n D a a' i).map fun e => decide (e ∈ P) := by
  unfold str
  exact List.map_congr_left fun e he => mark_st σ P (mem_tch_of_mem_tst he)
end VariableBound.Net.Val
