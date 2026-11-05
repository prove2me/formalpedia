-- Prove2me | solution 1 for SparsifyThenCount.stAlgSG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:30:01.427176+00:00
-- url     : https://prove2.me/submissions/5e9e47c1-3b3c-4b4e-a413-ee026b50f2de

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_Defs
import Definitions.Def_UniformInK_Top_End
import Definitions.Def_ClauseBound_Both_End
import Definitions.Def_SparsifyThenCount_Tied
import Theorems.Thm_ClauseBound_Both_End_steps_mono
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open SparsifyThenCount
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.Both.End UniformInK UniformInK.End VariableBound VariableBound.Decide
namespace SparsifyThenCount
theorem _root_.solution (hC : StCorrectBDG) (hK : StCertBDG) (hE : StExpBD) (hTD : StTimeD) (hTM : ClauseBound.Both.StTimeM) (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ) (hΘ : StepSparsify.Serves Θ Lc) :
    StAlgSG Θ := by
  intro Idx _ S e C₀ Q hS slU C hsl h1 h2 rn rm c₁ hrn hen hfb hrm hem _ _
  obtain ⟨hAB, heB⟩ := hK Θ Lc hΘ Idx S hS Q.pick slU Q.pick_poly hsl
  refine ⟨hAB, heB, fun k n φ hk hφ pad hp => hC Θ Lc hΘ Idx S e C₀ Q hS slU k n φ hk hφ pad hp, fun q => ?_, fun q => ?_⟩
  · obtain ⟨D, hD⟩ := hTD Idx S e C₀ Q hS slU C h1 h2 rn c₁ hrn hen hfb q
    exact ⟨D, fun k n φ hk hn1 hφ => (steps_mono q le_rfl (hE Idx S k Q.pick slU n φ hk hφ).1).trans (hD k n φ hk hn1 hφ)⟩
  · obtain ⟨D', hD'⟩ := hTM Idx S e C₀ Q hS rm c₁ hrm hem q
    exact ⟨D', fun k n φ hk hm1 hφ ho => (steps_mono q le_rfl ((hE Idx S k Q.pick slU n φ hk hφ).2 ho hm1)).trans (hD' k n φ hk hm1 hφ ho)⟩
end SparsifyThenCount
