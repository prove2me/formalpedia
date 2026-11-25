-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_hasFDerivAt_deriv_926a052cf6a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:18:28.83587+00:00
-- url     : https://prove2.me/submissions/edf53107-478d-4781-a1d8-80b383aca5c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IsConeAnalyticSubset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FderivFderivLogRho
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_hasFDerivAt_nsq_031169476c2f
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
    HasFDerivAt (fun z ↦ (nsq z)⁻¹ • bil z)
      ((nsq z)⁻¹ • bil + (((ContinuousLinearMap.toSpanSingleton ℝ (-(nsq z ^ 2)⁻¹)).comp
        ((2 : ℝ) • bil z))).smulRight (bil z)) z := by
  have hinv := (hasFDerivAt_inv (𝕜 := ℝ) (nsq_pos hz).ne').comp z (hasFDerivAt_nsq z)
  exact hinv.fun_smul bil.hasFDerivAt
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.FSLevi
