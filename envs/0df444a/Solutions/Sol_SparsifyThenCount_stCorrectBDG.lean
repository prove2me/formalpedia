-- Prove2me | solution 1 for SparsifyThenCount.stCorrectBDG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:29:36.469693+00:00
-- url     : https://prove2.me/submissions/95e986d9-08ce-4a2b-a0df-8e336d9ae4bc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_Defs
import Definitions.Def_VariableBound_Top_CorrectB
import Definitions.Def_SparsifyThenCount_CorrectB
import Theorems.Thm_VariableBound_CorrectB_useMD_enc


set_option autoImplicit false
section
section
open SparsifyThenCount
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound VariableBound.CorrectB
namespace SparsifyThenCount
theorem _root_.solution (h : StCorrectDG) (hM : StCorrectM) (hA : StAllOccU) (hD : StDecM) : StCorrectBDG := by
  intro Θ Lc hSv Idx _ S e C₀ Q hS slU k n φ hk hφ pad hpad
  change (bif useMD S Q.pick slU (SatM.enc k φ) then AM S Q.pick (SatM.enc k φ, pad) else ADG Θ S Q.pick slU (SatM.enc k φ, pad)) = _
  unfold eBD at hpad
  cases hu : useMD S Q.pick slU (SatM.enc k φ) with
  | true =>
    rw [hu, cond_true] at hpad
    rw [cond_true]
    obtain ⟨h1, h2, -⟩ := (useMD_enc hA hD S k Q.pick slU φ hk hφ).1 hu
    exact hM Idx S e C₀ Q hS k n φ hk h2 hφ h1 pad hpad
  | false =>
    rw [hu, cond_false] at hpad
    rw [cond_false]
    exact h Θ Lc hSv Idx S e C₀ Q hS slU k n φ hk hφ pad hpad
end SparsifyThenCount
