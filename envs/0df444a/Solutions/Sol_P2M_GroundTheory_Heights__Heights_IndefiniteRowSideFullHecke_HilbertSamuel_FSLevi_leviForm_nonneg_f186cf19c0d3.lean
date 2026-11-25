-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_leviForm_nonneg_f186cf19c0d3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:27:12.610125+00:00
-- url     : https://prove2.me/submissions/e904dbf2-afa4-4561-9651-67897eefd127

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IsConeAnalyticSubset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FderivFderivLogRho
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_bil_apply_07404f460fd9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_reP_apply_7da478929125
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_imaginaryPart_apply_dff8249560c5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_nsq_pos_10fd427978dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_fderiv_fderiv_logRho_2d89e81b4973
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_cs_011f677b3d11

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.FSLevi
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.FSLevi
theorem _root_.solution {z : J → ℂ} (hz : z ≠ 0) (w : J → ℂ) :
    0 ≤ leviForm (fun z ↦ Real.log ((fsMetric J).ρ z)) z w := by
  unfold leviForm
  rw [fderiv_fderiv_logRho hz]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  have hN := nsq_pos hz
  have hww : bil w w = nsq w := by
    rw [bil_apply, nsq]; exact Finset.sum_congr rfl fun p _ ↦ by ring
  have hiw : bil (Complex.I • w) (Complex.I • w) = nsq w := by
    rw [bil_apply, nsq]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp [reP_apply, imaginaryPart_apply]
    ring
  rw [hww, hiw]
  have hc := cs z w
  rw [← bil_apply, ← bil_apply] at hc
  set X := bil z w
  set Y := bil z (Complex.I • w)
  have key : (nsq z)⁻¹ * nsq w + (2 * X) * -(nsq z ^ 2)⁻¹ * X +
      ((nsq z)⁻¹ * nsq w + (2 * Y) * -(nsq z ^ 2)⁻¹ * Y) =
        2 * (nsq z * nsq w - (X ^ 2 + Y ^ 2)) / nsq z ^ 2 := by
    field_simp; ring
  have hnn : 0 ≤ 2 * (nsq z * nsq w - (X ^ 2 + Y ^ 2)) / nsq z ^ 2 :=
    div_nonneg (by linarith) (by positivity)
  have : 0 ≤ (nsq z)⁻¹ * nsq w + (2 * X) * -(nsq z ^ 2)⁻¹ * X +
      ((nsq z)⁻¹ * nsq w + (2 * Y) * -(nsq z ^ 2)⁻¹ * Y) := key ▸ hnn
  nlinarith [this]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.FSLevi
