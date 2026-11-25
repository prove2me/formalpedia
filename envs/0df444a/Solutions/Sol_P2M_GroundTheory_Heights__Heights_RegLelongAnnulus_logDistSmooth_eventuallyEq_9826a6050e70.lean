-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_logDistSmooth_eventuallyEq_9826a6050e70
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:48.369431+00:00
-- url     : https://prove2.me/submissions/272a8216-9c3e-4fe2-8d61-91d03dfe8974

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_distSq_a3573fb20031
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
theorem _root_.solution {r : ℝ} (hr : 0 < r) {z : Fin n → ℂ} (hz : r ^ 2 / 4 < euclPot (z - x)) :
    logDistSmooth x hr =ᶠ[𝓝 z] logDistSq x := by
  refine Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const (continuous_distSq x)).mem_nhds hz)
    fun z' hz' => ?_
  have h0 : smallBump hr (euclPot (z' - x)) = 0 :=
    (smallBump hr).zero_of_le_dist (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (distSq_nonneg x z')]
      exact (le_of_lt hz'))
  simp only [logDistSmooth, logDistSq]
  rw [h0, mul_zero, add_zero]
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
