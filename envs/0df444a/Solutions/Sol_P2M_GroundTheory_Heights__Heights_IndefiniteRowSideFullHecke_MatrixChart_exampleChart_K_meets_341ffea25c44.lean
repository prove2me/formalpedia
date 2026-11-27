-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_MatrixChart_exampleChart_K_meets_341ffea25c44
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:00:09.246328+00:00
-- url     : https://prove2.me/submissions/e042ee57-b9b3-4d82-aece-4ffdbaeb498f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_IsOpenKappaOpenNeighbourhood

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.MatrixChart
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.MatrixChart
theorem _root_.solution : ∃ p ∈ exampleChart.K, p.1 ∈ exampleChart.Ustar := by
  refine ⟨((fun _ => (1 / 2 : ℂ)), (fun _ => (0 : ℂ))), rfl, ?_, ?_⟩
  · show (fun _ => (1 / 2 : ℂ)) ∈ Metric.ball (0 : Fin 1 → ℂ) 1
    rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff (by norm_num)]
    intro i; norm_num
  · intro i; norm_num
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.MatrixChart
