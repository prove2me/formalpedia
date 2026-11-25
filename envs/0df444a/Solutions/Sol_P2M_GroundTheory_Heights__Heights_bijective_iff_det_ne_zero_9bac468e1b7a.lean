-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_bijective_iff_det_ne_zero_9bac468e1b7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:25:26.324577+00:00
-- url     : https://prove2.me/submissions/6cd8f805-2dc5-41f6-9288-9baee34efc1b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceMatricesOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGeneralProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceMatricesOpen

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
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {N : ℕ} (f : (Fin N → ℂ) →L[ℂ] (Fin N → ℂ)) :
    Function.Bijective f ↔ LinearMap.det (f : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)) ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot]
  exact ⟨fun h => h.1, fun h => ⟨h, LinearMap.injective_iff_surjective.1 h⟩⟩
end GroundTheory.Heights₂.Heights
