-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_hasFDerivAt_logRho_fbb4df6a8f7c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:56:47.83639+00:00
-- url     : https://prove2.me/submissions/40dc402c-45ad-4495-b33e-2e4188809609

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IsConeAnalyticSubset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FderivFderivLogRho
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_hasFDerivAt_nsq_031169476c2f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_log_rho_eq_e08da4724254
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_nsq_pos_10fd427978dc

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
theorem _root_.solution {z : J → ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun z ↦ Real.log ((fsMetric J).ρ z)) ((nsq z)⁻¹ • bil z) z := by
  have h := ((hasFDerivAt_nsq z).log (nsq_pos hz).ne').const_mul (1 / 2 : ℝ)
  have e : (fun z ↦ Real.log ((fsMetric J).ρ z)) = fun z ↦ (1 / 2) * Real.log (nsq z) :=
    funext log_rho_eq
  rw [e]
  refine h.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.FSLevi
