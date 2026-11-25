-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_support_log_iSup_place_finite_eb17bd99c37b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:40:48.615487+00:00
-- url     : https://prove2.me/submissions/cd3878dc-fd8d-4ef1-ad04-1f4b9520d22a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_hasFiniteMulSupport_iSup_place_6bf3c48ba8b2

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
open NumberField Module
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {F : Type*} [Field F] [NumberField F] {ι : Type*} [Finite ι]
    {y : ι → F} (hy : y ≠ 0) :
    (Function.support fun w : FinitePlace F ↦ Real.log (⨆ i, w (y i))).Finite := by
  refine Set.Finite.subset (hasFiniteMulSupport_iSup_place hy) fun w hw h1 ↦ hw ?_
  have h1' : (⨆ i, w (y i)) = 1 := h1
  change Real.log (⨆ i, w (y i)) = 0
  rw [h1', Real.log_one]
end GroundTheory.Heights₂.Heights
