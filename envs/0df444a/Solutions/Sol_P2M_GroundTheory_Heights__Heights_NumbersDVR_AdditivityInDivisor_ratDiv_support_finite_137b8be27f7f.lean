-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_ratDiv_support_finite_137b8be27f7f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:04.478117+00:00
-- url     : https://prove2.me/submissions/5b234698-74bf-498b-966c-396ac31d4d6b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_WithBotLtOfAddOneLe

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
open GroundTheory.Heights₂.Heights.NumbersDVR.AdditivityInDivisor
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.AdditivityInDivisor
theorem _root_.solution {P : Ideal (MRing ι R)} {f g : MRing ι R}
    (hf : (Function.support (divCycle P f)).Finite) (hg : (Function.support (divCycle P g)).Finite) :
    (Function.support (ratDiv P f g)).Finite := by
  refine (hf.union hg).subset fun W hW => ?_
  by_contra h
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
  exact hW (by simp [ratDiv, h.1, h.2])
end GroundTheory.Heights₂.Heights.NumbersDVR.AdditivityInDivisor
