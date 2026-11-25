-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_sheet_eventuallyEq_1d9f0375eb0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:48:09.511315+00:00
-- url     : https://prove2.me/submissions/477eee9c-8f97-4444-92cb-8bd727e90fd6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatSheetSumMeasurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ComplexSets
open GroundTheory.Heights₂.Heights.RatSheetSumMeasurable
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.RatSheetSumMeasurable
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} {x : Fin n → ℂ} {s s' : (Fin d → ℂ) → Fin n → ℂ}
    (hs : RatChart.IsRatSheetAt J p q x s) (hs' : RatChart.IsRatSheetAt J p q x s') :
    s' =ᶠ[𝓝 (RatChart.ratMap p q x)] s := by
  obtain ⟨U, hU, hxU, -, -, -, V, hV, hVs⟩ := hs
  obtain ⟨U', hU', hxU', hsd', hsx', hsec', -⟩ := hs'
  have hcont : ContinuousAt s' (RatChart.ratMap p q x) := hsd'.continuousOn.continuousAt (hU'.mem_nhds hxU')
  have h1 : ∀ᶠ w in 𝓝 (RatChart.ratMap p q x), s' w ∈ V :=
    hcont.preimage_mem_nhds (by rw [hsx']; exact hV)
  filter_upwards [h1, hU.mem_nhds hxU, hU'.mem_nhds hxU'] with w hwV hwU hwU'
  obtain ⟨hZ, hq, hR⟩ := hsec' w hwU'
  have h := hVs (s' w) ⟨hZ, hwV⟩ hq (by rw [hR]; exact hwU)
  rw [hR] at h
  exact h
end GroundTheory.Heights₂.Heights.RatSheetSumMeasurable
