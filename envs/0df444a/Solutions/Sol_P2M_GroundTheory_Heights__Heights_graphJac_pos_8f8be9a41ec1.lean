-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_graphJac_pos_8f8be9a41ec1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:37:12.467613+00:00
-- url     : https://prove2.me/submissions/9e05f9a5-dfb1-4705-ac57-cd263ebec5e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphJacContinuous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphJacContinuous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_one_add_adjoint_comp_self_pos_7ff02534c3e6

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
noncomputable section
open scoped InnerProductSpace
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {k m : ℕ} (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    0 < graphJac B :=
  Real.sqrt_pos.mpr (det_one_add_adjoint_comp_self_pos B)
end GroundTheory.Heights₂.Heights
