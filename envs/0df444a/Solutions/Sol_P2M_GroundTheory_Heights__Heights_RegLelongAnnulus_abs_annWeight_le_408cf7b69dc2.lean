-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_annWeight_le_408cf7b69dc2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:09.57977+00:00
-- url     : https://prove2.me/submissions/a304efaa-5da6-4227-b6ab-72cc7d3f8dff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus

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
variable {r s : ℝ} (e : ℕ)
namespace GroundTheory.Heights₂.Heights.RegLelongAnnulus
theorem _root_.solution (hr : 0 < r) (hs : 0 < s) (k : ℕ) (t : ℝ) :
    |annWeight r s e k t| ≤ r ^ (2 * (e + 1)) + s ^ (2 * (e + 1)) := by
  have hb : ∀ (c v : ℝ), 0 ≤ c → |c * hk k v| ≤ c := fun c v hc => by
    rw [abs_mul, abs_of_nonneg hc, abs_of_nonneg (hk k).nonneg]
    exact mul_le_of_le_one_right hc (hk k).le_one
  exact (abs_sub _ _).trans (add_le_add (hb _ _ (pow_nonneg hr.le _)) (hb _ _ (pow_nonneg hs.le _)))
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
