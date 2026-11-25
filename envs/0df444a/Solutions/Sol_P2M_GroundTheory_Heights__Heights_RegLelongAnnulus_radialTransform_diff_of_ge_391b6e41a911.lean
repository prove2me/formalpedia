-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_diff_of_ge_391b6e41a911
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:49:09.235635+00:00
-- url     : https://prove2.me/submissions/ef13b32b-1677-43ae-b88e-38a938114f29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_hk_of_one_le_ce02361cae31

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
theorem _root_.solution (hr : 0 < r) (hrs : r ≤ s) (k : ℕ) {t : ℝ} (ht : s ^ 2 ≤ t) :
    radialTransform (e + 1) (hk k) (t / s ^ 2) - radialTransform (e + 1) (hk k) (t / r ^ 2) = 0 := by
  have hr2 := pow_pos hr 2
  have hs2 : r ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hr.le hrs 2
  rw [radialTransform_hk_of_one_le e k ((one_le_div (hr2.trans_le hs2)).2 ht),
    radialTransform_hk_of_one_le e k ((one_le_div hr2).2 (hs2.trans ht)), sub_self]
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
