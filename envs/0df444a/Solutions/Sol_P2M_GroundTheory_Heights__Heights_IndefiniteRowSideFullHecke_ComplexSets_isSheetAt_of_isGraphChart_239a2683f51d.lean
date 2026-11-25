-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isSheetAt_of_isGraphChart_239a2683f51d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:56:56.006151+00:00
-- url     : https://prove2.me/submissions/e17ef262-9cd4-4a0f-a332-d1fe9b947578

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
theorem _root_.solution {σ : (Fin d → ℂ) → Fin n → ℂ}
    (h : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsGraphChart J A x σ) :
    GroundTheory.Heights₂.Heights.IsSheetAt J A x σ := by
  obtain ⟨hx, U, V, hU, hxU, hV, han, hbij, hsec⟩ := h
  obtain ⟨w, hwV, hw⟩ := hbij.surjOn ⟨hx, hxU⟩
  have hAx : A *ᵥ x = w := by rw [← hw]; exact hsec w hwV
  refine ⟨V, hV, by rw [hAx]; exact hwV, han.differentiableOn, by rw [hAx, hw],
    fun y hy => ⟨hsec y hy, (hbij.mapsTo hy).1⟩, U, hU.mem_nhds hxU, ?_⟩
  rintro x' ⟨hx'Z, hx'U⟩ _
  obtain ⟨w', hw'V, hw'⟩ := hbij.surjOn ⟨hx'Z, hx'U⟩
  have hA' : A *ᵥ x' = w' := by rw [← hw']; exact hsec w' hw'V
  rw [hA', hw']
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
