-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_annWeight_const_bf676f231701
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:10.708613+00:00
-- url     : https://prove2.me/submissions/ad4c1f3b-82b6-47d6-aae5-51d8af69bd11

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_hk_one_b52240beee02

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
theorem _root_.solution (hr : 0 < r) (hrs : r ≤ s) (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 (pk k * r ^ 2)) :
    annWeight r s e k t = annWeight r s e k 0 := by
  have hr2 := pow_pos hr 2
  have hs2 : r ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hr.le hrs 2
  have h1 : t / r ^ 2 ≤ pk k := (div_le_iff₀ hr2).2 ht.2
  have h2 : t / s ^ 2 ≤ t / r ^ 2 := div_le_div_of_nonneg_left ht.1 hr2 hs2
  unfold annWeight
  rw [hk_one (div_nonneg ht.1 (hr2.trans_le hs2).le) (h2.trans h1), hk_one (div_nonneg ht.1 hr2.le) h1,
    zero_div, zero_div, hk_one le_rfl (pk_pos k).le]
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
