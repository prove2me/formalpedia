-- Prove2me | solution 1 for VariableBound.stExpBD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:29:35.444025+00:00
-- url     : https://prove2.me/submissions/89ab36ff-eb36-44be-b566-59daab52fc9b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_VariableBound_Top_CorrectB
import Theorems.Thm_VariableBound_CorrectB_useMD_enc

set_option autoImplicit false
section
section
open VariableBound
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound.CorrectB
namespace VariableBound
theorem _root_.solution (hA : StAllOccU) (hD : StDecM) : StExpBD := by
  intro Idx _ S k pick slU n φ hk hφ
  have hiff := useMD_enc hA hD S k pick slU φ hk hφ
  unfold eBD
  cases hu : useMD S pick slU (SatM.enc k φ) with
  | true =>
    rw [cond_true]
    exact ⟨(hiff.1 hu).2.2, fun _ _ => le_rfl⟩
  | false =>
    rw [cond_false]
    refine ⟨le_rfl, fun h1 h2 => ?_⟩
    by_contra hlt
    have h3 := hiff.2 ⟨h1, h2, (not_le.1 hlt).le⟩
    rw [hu] at h3
    cases h3
end VariableBound
