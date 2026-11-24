-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_diff_of_le_d2a53db5a632
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:21.802307+00:00
-- url     : https://prove2.me/submissions/a1fb5dba-f29c-4b62-8ab8-6bf3034869fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_hk_of_le_64a107755ae3

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
theorem _root_.solution (hr : 0 < r) (hrs : r ≤ s) (k : ℕ) {t : ℝ} (h0 : 0 ≤ t)
    (ht : t ≤ pk k * r ^ 2) :
    radialTransform (e + 1) (hk k) (t / s ^ 2) - radialTransform (e + 1) (hk k) (t / r ^ 2) = 0 := by
  have hr2 := pow_pos hr 2
  have hs2 : r ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hr.le hrs 2
  have h1 : t / r ^ 2 ≤ pk k := (div_le_iff₀ hr2).2 ht
  have h2 : t / s ^ 2 ≤ t / r ^ 2 := div_le_div_of_nonneg_left h0 hr2 hs2
  rw [radialTransform_hk_of_le e k (div_nonneg h0 (hr2.trans_le hs2).le) (h2.trans h1),
    radialTransform_hk_of_le e k (div_nonneg h0 hr2.le) h1, sub_self]
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
