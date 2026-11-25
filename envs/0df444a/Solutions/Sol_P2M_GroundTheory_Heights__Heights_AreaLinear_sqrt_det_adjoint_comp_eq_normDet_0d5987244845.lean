-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AreaLinear_sqrt_det_adjoint_comp_eq_normDet_0d5987244845
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:39:33.352395+00:00
-- url     : https://prove2.me/submissions/b0624819-9b7e-40e6-aeac-fd4a092ea7de

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaLinear

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
open MeasureTheory Module
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace AreaLinear
theorem _root_.solution {k m : ℕ}
    (L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    √(LinearMap.det (LinearMap.adjoint L ∘ₗ L)) = L.normDet := by
  rw [← LinearMap.normDet_sq L]
  push_cast
  exact Real.sqrt_sq (LinearMap.normDet_nonneg L)
end AreaLinear
end GroundTheory.Heights₂.Heights
