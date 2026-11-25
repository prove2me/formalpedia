-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KRest_smallPowerSum_isHomogeneous_cdf6a1058f11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:33.43974+00:00
-- url     : https://prove2.me/submissions/058d60d3-3a68-4aff-9901-d66e3aa8bbcc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutCaseSharp

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace KRest
theorem _root_.solution (f r a : ℕ) (cs : RestTerms.SmallBlock) (n : ℕ) (τ : Fin f) :
    (RestTerms.smallPowerSum f r a cs n τ).IsHomogeneous n :=
  IsHomogeneous.sum _ _ _ fun i _ => by
    simpa [RestTerms.yRoot] using ((isHomogeneous_C_mul_X (R := ℚ) _ (RestTerms.yIndex f r a cs τ i)).pow n)
end KRest
end GroundTheory.Heights₂.Heights
