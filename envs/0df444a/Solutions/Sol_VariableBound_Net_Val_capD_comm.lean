-- Prove2me | solution 1 for VariableBound.Net.Val.capD_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:27:25.185129+00:00
-- url     : https://prove2.me/submissions/ac19e2e3-4851-4537-9092-40c055090557

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
import Theorems.Thm_VariableBound_Net_Val_tst_comm
import Theorems.Thm_VariableBound_Net_Val_mu_comm
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_PaddedDescent_F_Mark_Prof_mu_comm
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL ext)
variable {k g n : ℕ} {D : Dat} {y : ℕ} {fl : Bool}
namespace VariableBound.Net.Val
theorem _root_.solution (a a' : ℕ) : capD g n D y a a' = capD g n D y a' a := by
  unfold capD
  refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
  rw [mu_comm, tst_comm]
end VariableBound.Net.Val
