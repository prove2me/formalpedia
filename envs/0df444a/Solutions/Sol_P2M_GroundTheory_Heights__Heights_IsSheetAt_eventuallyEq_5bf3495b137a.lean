-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IsSheetAt_eventuallyEq_5bf3495b137a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:17:09.562934+00:00
-- url     : https://prove2.me/submissions/eec2aa1b-d05b-4618-8900-dac394496786

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSliceSheetParam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeSheetGramLintegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Filter Topology Set ComplexSets
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace IsSheetAt
theorem _root_.solution {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ} {γ s : (Fin d → ℂ) → Fin n → ℂ}
    (hγ : IsSheetAt J A x γ) (hs : IsSheetAt J A x s) : γ =ᶠ[𝓝 (A *ᵥ x)] s := by
  obtain ⟨U, hU, hxU, hγd, hγx, hγZ, -⟩ := hγ
  obtain ⟨U', hU', hxU', -, -, -, V, hV, hsV⟩ := hs
  have hc : ContinuousAt γ (A *ᵥ x) := (hγd.differentiableAt (hU.mem_nhds hxU)).continuousAt
  have hV' : ∀ᶠ y in 𝓝 (A *ᵥ x), γ y ∈ V := hc.preimage_mem_nhds (by rwa [hγx])
  filter_upwards [hU.mem_nhds hxU, hU'.mem_nhds hxU', hV'] with y hy hy' hyV
  obtain ⟨hAy, hZy⟩ := hγZ y hy
  have h := hsV (γ y) ⟨hZy, hyV⟩ (by rwa [hAy])
  rwa [hAy] at h
end IsSheetAt
end GroundTheory.Heights₂.Heights
