-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_LogIntegrableOn_to_current_fdbd3f1f4063
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:32:55.729958+00:00
-- url     : https://prove2.me/submissions/8d397b7d-3819-4b89-876d-6aedf1455eed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsSheetMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isFiniteProj_iff_2c15bda3c982
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_projIntegrable_iff_fd71fe26c6a1


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
open MvPolynomial MeasureTheory Filter
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace LogIntegrableOn
theorem _root_.solution (h : LogIntegrableOn.Statement) :
    GroundTheory.Heights₂.Heights.LogIntegrable.Statement := by
  intro n d J A u φ R hJ hdim hA hu hφ
  have hJ' : IsAffVariety J d := ⟨hJ, hdim⟩
  exact (projIntegrable_iff _ _ _ _).mp
    (h n d J A φ u (Metric.closedBall 0 R) hJ' ((isFiniteProj_iff hJ').mpr hA) hφ hu
      measurableSet_closedBall Metric.isBounded_closedBall)
end LogIntegrableOn
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
