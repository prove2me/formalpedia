-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ReducedCut_length_quot_map_mk_1149da282bdc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:14:56.255797+00:00
-- url     : https://prove2.me/submissions/540374b5-ab37-42c2-939b-740decb7bcb0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsReducedCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OrdModEqLengthQuotSup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PReducedCutLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open GroundTheory.Heights₂.Heights.Inter.ReducedCut
open IsLocalRing
namespace GroundTheory.Heights₂.Heights.Inter.ReducedCut
theorem _root_.solution {L : Type*} [CommRing L] (J₀ J : Ideal L) :
    Module.length (L ⧸ J₀) ((L ⧸ J₀) ⧸ J.map (Ideal.Quotient.mk J₀)) =
      Module.length L (L ⧸ (J₀ ⊔ J)) := by
  rw [← Module.length_eq_of_surjective (S := L) Ideal.Quotient.mk_surjective]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ L J₀ J).toLinearEquiv.length_eq
end GroundTheory.Heights₂.Heights.Inter.ReducedCut
