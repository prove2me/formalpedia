-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_distSq_add_pos_20ae4db78bb9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:48:30.854079+00:00
-- url     : https://prove2.me/submissions/66743b1f-82d0-4345-b21b-cfbbb3960a62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_distSq_nonneg_983e714bd225

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
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegLelongAnnulus
variable {n : ℕ} (x : Fin n → ℂ)
namespace GroundTheory.Heights₂.Heights.RegLelongAnnulus
theorem _root_.solution {r : ℝ} (hr : 0 < r) (z : Fin n → ℂ) :
    0 < euclPot (z - x) + r ^ 2 * smallBump hr (euclPot (z - x)) := by
  have h0 := distSq_nonneg x z
  have hr2 := pow_pos hr 2
  rcases le_or_gt (euclPot (z - x)) (r ^ 2 / 8) with h | h
  · have h1 : smallBump hr (euclPot (z - x)) = 1 :=
      (smallBump hr).one_of_mem_closedBall (by
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg h0]
        exact h)
    rw [h1]
    linarith
  · have := (smallBump hr).nonneg (x := euclPot (z - x))
    have : 0 ≤ r ^ 2 * smallBump hr (euclPot (z - x)) := mul_nonneg hr2.le this
    linarith [pow_pos hr 2]
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
