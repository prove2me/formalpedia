-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_sheet_eventuallyEq_f5b44630f2f2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:08.13016+00:00
-- url     : https://prove2.me/submissions/4d1488d6-f27c-4117-80f4-7e863992a712

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsSheetMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.SheetSumMeasurable
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.SheetSumMeasurable
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s s' : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s)
    (hs' : IsSheetAt J A x s') : s' =ᶠ[𝓝 (A *ᵥ x)] s := by
  obtain ⟨U, hU, hxU, -, -, -, V, hV, hVs⟩ := hs
  obtain ⟨U', hU', hxU', hsd', hsx', hsec', -⟩ := hs'
  have hcont : ContinuousAt s' (A *ᵥ x) := hsd'.continuousOn.continuousAt (hU'.mem_nhds hxU')
  have h1 : ∀ᶠ w in 𝓝 (A *ᵥ x), s' w ∈ V := hcont.preimage_mem_nhds (by rw [hsx']; exact hV)
  filter_upwards [h1, hU.mem_nhds hxU, hU'.mem_nhds hxU'] with w hwV hwU hwU'
  have h := hVs (s' w) ⟨(hsec' w hwU').2, hwV⟩ (by rw [(hsec' w hwU').1]; exact hwU)
  rw [(hsec' w hwU').1] at h
  exact h
end GroundTheory.Heights₂.Heights.SheetSumMeasurable
