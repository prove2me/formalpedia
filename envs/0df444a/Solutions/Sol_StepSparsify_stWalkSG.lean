-- Prove2me | solution 1 for StepSparsify.stWalkSG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:34:39.80644+00:00
-- url     : https://prove2.me/submissions/2866524e-6cb5-4714-beb7-36eb8bec0f0e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_CountKSatRate_Walk
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_StepSparsify_Walk
import Theorems.Thm_CountKSatRate_roundS_iterate_of_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_PaddedDescent_F_Top_foldl_capped_eq_iterate
import Theorems.Thm_PaddedDescent_F_cap_eq
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open StepSparsify
open Groundwork Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F CountKSatRate UniformInK
namespace StepSparsify
theorem _root_.solution : StWalkSG := by
  intro θ k pad val r d hd hlen hst
  unfold walkSG
  rw [Top.foldl_capped_eq_iterate (cap pad ([], 0)) (roundS (stepC θ k) val) (fun x => len x ≤ pad.length)
    (fun x hx => cap_eq hx) pad ([r], 0) (fun i _ => hst i),
    roundS_iterate_of_le (stepC θ k) val d r hd pad.length (by omega)]
end StepSparsify
