-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_pk_pow_le_Ik_fbb0273b26eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:40.856311+00:00
-- url     : https://prove2.me/submissions/d7d67643-086c-4236-8dc4-0342f9a6361a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_kernel_nonneg_9afb1b251b85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_pk_le_one_bc32229bb89c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_hk_one_b52240beee02
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
theorem _root_.solution (e k : ℕ) : pk k ^ (e + 1) ≤ Ik e k := by
  unfold Ik
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := pk k)
    ((continuous_hk_kernel e k).intervalIntegrable _ _) ((continuous_hk_kernel e k).intervalIntegrable _ _)]
  have h1 : ∫ w in (0 : ℝ)..pk k, hk k w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) = pk k ^ (e + 1) := by
    rw [← integral_kernel e (pk k)]
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [Set.uIcc_of_le (pk_pos k).le] at hw
    rw [hk_one hw.1 hw.2]
  have h2 : 0 ≤ ∫ w in pk k..1, hk k w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) :=
    intervalIntegral.integral_nonneg (pk_le_one k)
      fun w hw => mul_nonneg (hk k).nonneg (kernel_nonneg e ((pk_pos k).le.trans hw.1))
  linarith
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
