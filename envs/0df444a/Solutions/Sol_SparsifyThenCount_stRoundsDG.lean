-- Prove2me | solution 1 for SparsifyThenCount.stRoundsDG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:29:04.161371+00:00
-- url     : https://prove2.me/submissions/562e471a-b6b6-44d3-9ed6-da9c8d601f90

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_Defs
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_VariableBound_Top_Correct
import Definitions.Def_VariableBound_Top_Correct
import Definitions.Def_SparsifyThenCount_Correct
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open SparsifyThenCount
open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK UniformInK.Correct VariableBound VariableBound.Correct VariableBound.Net
open PaddedDescent.F.Mark (WfL occ nSat)
namespace SparsifyThenCount
theorem _root_.solution : StRoundsDG := by
  intro k K n s F hF
  have h1 : n / 2 ^ s + 1 + 1 ≤ restD k K n s := by unfold restD; omega
  have h2 : 2 ^ (n / 2 ^ s + 1 + 1) ≤ F := (Nat.pow_le_pow_right (by norm_num) h1).trans hF
  rw [pow_succ] at h2
  omega
end SparsifyThenCount
