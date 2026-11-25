-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isNilpotent_of_minimalPrimes_eq_singleton_06d31625bdb3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:34:30.380836+00:00
-- url     : https://prove2.me/submissions/8105021e-b3b4-4fe9-8f55-18a58e8e4968

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutLocalizedModule
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PLocalizedQuotLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthLocalizedQuotient

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
universe u
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {B : Type*} [CommRing B] [IsNoetherianRing B] {P : Ideal B}
    (hmin : minimalPrimes B = {P}) : IsNilpotent P := by
  have h : sInf (minimalPrimes B) = nilradical B := Ideal.sInf_minimalPrimes
  rw [hmin, sInf_singleton] at h
  rw [h]
  exact IsNoetherianRing.isNilpotent_nilradical B
end GroundTheory.Heights₂.Heights
