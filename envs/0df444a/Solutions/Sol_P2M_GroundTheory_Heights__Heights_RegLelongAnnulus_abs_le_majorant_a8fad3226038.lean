-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_le_majorant_a8fad3226038
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:38.9368+00:00
-- url     : https://prove2.me/submissions/d4a7a5b2-ac38-447a-9b97-0da39ad028cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_majorant_nonneg_fa1e6daa9762
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_majorant_one_2d3599a009c6

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
theorem _root_.solution {s C : ℝ} (hC : 0 ≤ C) {w : (Fin n → ℂ) → ℝ} (hw : ∀ z, |w z| ≤ C)
    (h0 : ∀ z, s ^ 2 ≤ euclPot (z - x) → w z = 0) (z : Fin n → ℂ) : |w z| ≤ C * majorant x s z := by
  rcases le_or_gt (s ^ 2) (euclPot (z - x)) with h | h
  · rw [h0 z h, abs_zero]
    exact mul_nonneg hC (majorant_nonneg x s z)
  · rw [majorant_one x h.le, mul_one]
    exact hw z
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
