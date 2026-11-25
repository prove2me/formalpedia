-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_primeTube_isClosed_zeroSetEuc_7d65982b96e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:36:51.699833+00:00
-- url     : https://prove2.me/submissions/cf560533-1336-4940-b8bd-90b273246dce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyMassLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSmallSetBallCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeTubeVolume

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
open MvPolynomial MeasureTheory ComplexSets Metric
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsClosed (zeroSetEuc J) := by
  have : zeroSetEuc J = ⋂ q ∈ J, {z : EuclideanSpace ℂ (Fin n) | eval (fun i => z i) q = 0} := by
    ext z; simp [zeroSetEuc]
  rw [this]
  exact isClosed_biInter fun q _ =>
    isClosed_eq ((MvPolynomial.continuous_eval q).comp (PiLp.continuous_ofLp 2 _)) continuous_const
end GroundTheory.Heights₂.Heights
