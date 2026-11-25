-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_fderiv_fderiv_logRho_2d89e81b4973
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:43.890799+00:00
-- url     : https://prove2.me/submissions/e0039211-59be-4646-99fc-d9ff16d8c1c0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IsConeAnalyticSubset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FderivFderivLogRho
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_hasFDerivAt_logRho_fbb4df6a8f7c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_hasFDerivAt_deriv_926a052cf6a9

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
    fderiv ℝ (fderiv ℝ fun z ↦ Real.log ((fsMetric J).ρ z)) z =
      (nsq z)⁻¹ • bil + (((ContinuousLinearMap.toSpanSingleton ℝ (-(nsq z ^ 2)⁻¹)).comp
        ((2 : ℝ) • bil z))).smulRight (bil z) := by
  have hev : (fderiv ℝ fun z ↦ Real.log ((fsMetric J).ρ z)) =ᶠ[nhds z]
      fun z ↦ (nsq z)⁻¹ • bil z := by
    filter_upwards [isOpen_ne.mem_nhds hz] with z' hz'
    exact (hasFDerivAt_logRho hz').fderiv
  rw [hev.fderiv_eq]
  exact (hasFDerivAt_deriv hz).fderiv
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.FSLevi
