-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_hasCompactSupport_majorant_a1a537fd70d7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:46.608801+00:00
-- url     : https://prove2.me/submissions/fc3394b5-97fb-4155-9687-159c5311759d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_distSq_nonneg_983e714bd225
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_norm_sub_le_sqrt_05eff018e747

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
theorem _root_.solution (s : ℝ) : HasCompactSupport (majorant x s) := by
  refine HasCompactSupport.intro (isCompact_closedBall x (2 * (s ^ 2 + 1))) fun z hz => ?_
  rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hz
  have hR : 1 ≤ 2 * (s ^ 2 + 1) := by nlinarith [sq_nonneg s]
  have h1 : 2 * (s ^ 2 + 1) < Real.sqrt (euclPot (z - x)) := hz.trans_le (norm_sub_le_sqrt x z)
  have h2 : (2 * (s ^ 2 + 1)) ^ 2 < euclPot (z - x) := (Real.lt_sqrt (by linarith)).1 h1
  refine (bigBump s).zero_of_le_dist ?_
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (distSq_nonneg x z)]
  show 2 * (s ^ 2 + 1) ≤ euclPot (z - x)
  nlinarith
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
