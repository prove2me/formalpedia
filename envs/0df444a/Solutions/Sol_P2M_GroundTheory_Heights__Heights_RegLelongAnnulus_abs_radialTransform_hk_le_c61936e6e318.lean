-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_radialTransform_hk_le_c61936e6e318
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:56:21.187822+00:00
-- url     : https://prove2.me/submissions/0f7af0a6-18b1-4251-980f-7b9c36f5a551

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_hk_of_one_le_ce02361cae31
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_hk_le_65497141e8ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_hk_nonneg_301de9d1902f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_Ik_le_one_c5e9977958ee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_Ik_nonneg_49cc97c700fa

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
    |radialTransform (e + 1) (hk k) v| ≤ 1 := by
  rcases le_or_gt 1 v with h1 | h1
  · rw [radialTransform_hk_of_one_le e k h1, abs_neg, abs_of_nonneg (Ik_nonneg e k)]
    exact Ik_le_one e k
  · unfold radialTransform
    have hv1 : v ^ (e + 1) ≤ 1 := pow_le_one₀ h0 h1.le
    have ha0 : 0 ≤ hk k v * v ^ (e + 1) := mul_nonneg (hk k).nonneg (pow_nonneg h0 _)
    have ha1 : hk k v * v ^ (e + 1) ≤ 1 := mul_le_one₀ (hk k).le_one (pow_nonneg h0 _) hv1
    have hb0 := integral_hk_nonneg e k h0
    have hb1 := (integral_hk_le e k h0).trans hv1
    rw [abs_le]
    constructor <;> linarith
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
