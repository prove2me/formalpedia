-- Prove2me | solution 1 for UniformInK.Correct.kcU_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:25:32.171893+00:00
-- url     : https://prove2.me/submissions/1791fe2c-9efe-4e98-bee9-31602ac3a9bf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_ClauseBound_ParityChecks_TopOL
import Definitions.Def_ClauseBound_ParityChecks_TopOL
import Definitions.Def_UniformInK_Top_Correct
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open UniformInK UniformInK.Correct
open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.ParityChecks.TopOL
open PaddedDescent.F.Mark (WfL occ nSat)
namespace UniformInK.Correct
theorem _root_.solution {k n s : ℕ} (h : 2 ^ betaU k s ≤ n + 1) : kcU k n = k := by
  refine min_eq_left (Nat.le_log_of_pow_le (by norm_num) (le_trans (Nat.pow_le_pow_right (by norm_num) ?_) h))
  unfold betaU
  nlinarith [Nat.zero_le (k * s)]
end UniformInK.Correct
