-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_graphChart_eventuallyEq_sheet_3b642567994b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:56:44.564799+00:00
-- url     : https://prove2.me/submissions/05975366-30f2-4201-be08-bfc19da33804

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial MeasureTheory Filter Topology Matrix
noncomputable section
variable {n d : ℕ}
variable {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ s : (Fin d → ℂ) → Fin n → ℂ}
    (hσ : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsGraphChart J A x σ)
    (hs : GroundTheory.Heights₂.Heights.IsSheetAt J A x s) : σ =ᶠ[𝓝 (A *ᵥ x)] s := by
  obtain ⟨-, U, V, hU, hxU, -, -, hbij, hsec⟩ := hσ
  obtain ⟨W, hW, hAxW, hsd, hsx, hssec, -⟩ := hs
  have hcont : ContinuousAt s (A *ᵥ x) := hsd.continuousOn.continuousAt (hW.mem_nhds hAxW)
  have h1 : ∀ᶠ y in 𝓝 (A *ᵥ x), s y ∈ U :=
    hcont.preimage_mem_nhds (by rw [hsx]; exact hU.mem_nhds hxU)
  have h2 : ∀ᶠ y in 𝓝 (A *ᵥ x), y ∈ W := hW.mem_nhds hAxW
  filter_upwards [h1, h2] with y hyU hyW
  obtain ⟨w, hwV, hw⟩ := hbij.surjOn ⟨(hssec y hyW).2, hyU⟩
  have hwy : w = y := by rw [← hsec w hwV, hw, (hssec y hyW).1]
  rw [hwy] at hw
  exact hw
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
