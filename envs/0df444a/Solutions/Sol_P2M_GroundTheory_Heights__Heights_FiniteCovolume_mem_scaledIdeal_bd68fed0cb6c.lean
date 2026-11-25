-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_scaledIdeal_bd68fed0cb6c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:12:08.903463+00:00
-- url     : https://prove2.me/submissions/04d5bef1-ce01-4ed1-85b6-3a3c4a001663

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIdealClassesFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField
variable {E : Type*} [Field E] [NumberField E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {I : AddSubgroup E} {hI : ∀ a : 𝓞 E, ∀ x ∈ I, (a : E) * x ∈ I} {b : E}
    {y : 𝓞 E} : y ∈ scaledIdeal I hI b ↔ b⁻¹ * (y : E) ∈ I := Iff.rfl
end GroundTheory.Heights₂.Heights.FiniteCovolume
