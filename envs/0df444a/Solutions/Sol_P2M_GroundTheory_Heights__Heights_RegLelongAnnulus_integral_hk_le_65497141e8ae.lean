-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_hk_le_65497141e8ae
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:49.887433+00:00
-- url     : https://prove2.me/submissions/b0d5aafb-f78e-4ef3-83c8-db8ed44fb172

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_kernel_66dd3acd1271
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_kernel_nonneg_9afb1b251b85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_hk_kernel_8d22d3ab3230
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_kernel_6618981a4f14

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
namespace GroundTheory.Heights₂.Heights.RegLelongAnnulus
theorem _root_.solution (e k : ℕ) {v : ℝ} (h0 : 0 ≤ v) :
    ∫ w in (0 : ℝ)..v, hk k w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) ≤ v ^ (e + 1) := by
  rw [← integral_kernel e v]
  exact intervalIntegral.integral_mono_on h0 ((continuous_hk_kernel e k).intervalIntegrable _ _)
    ((continuous_const.mul (continuous_kernel e)).intervalIntegrable _ _)
    fun w hw => mul_le_mul_of_nonneg_right (hk k).le_one (kernel_nonneg e hw.1)
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
