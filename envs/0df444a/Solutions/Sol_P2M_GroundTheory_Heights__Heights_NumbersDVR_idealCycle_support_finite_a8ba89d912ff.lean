-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_idealCycle_support_finite_a8ba89d912ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:28.58624+00:00
-- url     : https://prove2.me/submissions/139b0158-af06-4146-973a-f1579202febd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivisorIdealBotUniformiser
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleFiniteSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IdealCycleSupportFinite

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
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
    [IsNoetherianRing (MRing ι R)] (J : Ideal (MRing ι R)) :
    (Function.support (idealCycle J)).Finite := by
  apply Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing _ J)
  intro W hW
  by_contra hmin
  apply hW
  unfold idealCycle
  rw [dif_neg]
  exact fun h => hmin h.1
end GroundTheory.Heights₂.Heights.NumbersDVR
