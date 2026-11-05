-- Prove2me | solution 1 for PairsToBound.half_le_inv_sqrt_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:59:15.636206+00:00
-- url     : https://prove2.me/submissions/0fc83300-4fd4-4338-a94a-28e1d442fe26

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_GeneralPieces_Rec_Seq
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Rec_Rate
import Definitions.Def_GeneralPieces_Rec_PartB
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_PairsToBound_Pairs

set_option autoImplicit false
section
section
open PairsToBound
open Turing Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Seq Levels.Gen GeneralPieces MainTheoremForms
namespace PairsToBound
theorem _root_.solution : (1 : ℝ) / 2 ≤ 1 / Real.sqrt 2 ∧ 1 / Real.sqrt 2 < 1 := by
  have h0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  refine ⟨one_div_le_one_div_of_le h0 (by nlinarith), ?_⟩
  rw [div_lt_one h0]
  nlinarith
end PairsToBound
