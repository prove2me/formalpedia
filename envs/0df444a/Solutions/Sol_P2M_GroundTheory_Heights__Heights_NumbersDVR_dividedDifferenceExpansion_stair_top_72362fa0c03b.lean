-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_stair_top_72362fa0c03b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:01.757848+00:00
-- url     : https://prove2.me/submissions/fff45c30-d62a-439d-a98f-3b2051ba0800

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
theorem _root_.solution {r : ℕ} (μ : Fin r →₀ ℕ) : stair μ r = ∏ j, X (Sum.inr j) ^ μ j := by
  simp [stair]
end GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion
