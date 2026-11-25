-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_stair_zero_d0e94a0e87e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:05.387626+00:00
-- url     : https://prove2.me/submissions/302ed1ae-4b58-4f92-85bf-be806e787b7b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinDivDiffExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion
namespace GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion
theorem _root_.solution {r : ℕ} (μ : Fin r →₀ ℕ) : stair μ 0 = ∏ j, X (Sum.inl j) ^ μ j := by
  simp [stair]
end GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion
