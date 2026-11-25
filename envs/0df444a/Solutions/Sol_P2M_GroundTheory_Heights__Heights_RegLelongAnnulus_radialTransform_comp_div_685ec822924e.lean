-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_comp_div_685ec822924e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:41:52.106265+00:00
-- url     : https://prove2.me/submissions/11bff0c5-cf43-4b99-8a5e-82d9c6e08b0a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_comp_div_sq_378fa9759947

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
theorem _root_.solution (e : ℕ) (h : ℝ → ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) (t : ℝ) :
    radialTransform (e + 1) (fun τ => h (τ / ρ ^ 2)) t =
      ρ ^ (2 * (e + 1)) * radialTransform (e + 1) h (t / ρ ^ 2) := by
  unfold radialTransform
  beta_reduce
  rw [integral_comp_div_sq e h hρ t]
  have ht : t ^ (e + 1) = ρ ^ (2 * (e + 1)) * (t / ρ ^ 2) ^ (e + 1) := by
    rw [div_pow, ← pow_mul]
    field_simp
  rw [ht]
  ring
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
