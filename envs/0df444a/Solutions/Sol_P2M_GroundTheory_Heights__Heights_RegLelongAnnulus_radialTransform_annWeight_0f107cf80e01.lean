-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_annWeight_0f107cf80e01
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:51:19.217799+00:00
-- url     : https://prove2.me/submissions/5d778587-7a71-40f5-9c05-ea67b06c24a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_comp_div_685ec822924e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_sub_8677133a77df

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
    radialTransform (e + 1) (annWeight r s e k) t =
      r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
        (radialTransform (e + 1) (hk k) (t / s ^ 2) - radialTransform (e + 1) (hk k) (t / r ^ 2)) := by
  rw [show annWeight r s e k =
      (fun τ => r ^ (2 * (e + 1)) * hk k (τ / s ^ 2) - s ^ (2 * (e + 1)) * hk k (τ / r ^ 2)) from rfl,
    radialTransform_sub e (f₁ := fun τ => hk k (τ / s ^ 2)) (f₂ := fun τ => hk k (τ / r ^ 2))
      ((hk k).continuous.comp (continuous_id.div_const _)) ((hk k).continuous.comp (continuous_id.div_const _)),
    radialTransform_comp_div e (hk k) hs.ne', radialTransform_comp_div e (hk k) hr.ne']
  ring
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
