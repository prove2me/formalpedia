-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticOnNhd_of_differentiableOn_d56f1b066651
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:38:09.709938+00:00
-- url     : https://prove2.me/submissions/5416bc21-ed58-40df-b903-ec606a8d43d7

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {U : Set (Fin d → ℂ)} {s : (Fin d → ℂ) → Fin n → ℂ}
    (hU : IsOpen U) (hs : DifferentiableOn ℂ s U) : AnalyticOnNhd ℂ s U := by
  have h : ∀ j, AnalyticOnNhd ℂ (fun y => s y j) U := fun j =>
    ReciprocityTheory.AnForm.Osgood.osgood d U _ hU (differentiableOn_pi.mp hs j)
  exact AnalyticOnNhd.pi h
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
