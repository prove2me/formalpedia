-- Prove2me | solution 1 for PI.DIP.NormOne.map_mem_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:34:54.387949+00:00
-- url     : https://prove2.me/submissions/32b40301-811b-4388-8e7a-c9c5c9307674

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DetIdPG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_StNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_NormOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors
open PI PI.DIP PI.DIP.NormOne
variable {E : Type} [Field E] [NumberField E]
namespace PI.DIP.NormOne
theorem _root_.solution (c : E →+* E) {P P' Q Q' : Submodule (𝓞 E) E}
    (h : ∀ p ∈ P, c p ∈ Q) (h' : ∀ p ∈ P', c p ∈ Q') : ∀ w ∈ P * P', c w ∈ Q * Q' := by
  intro w hw
  refine Submodule.mul_induction_on (C := fun w => c w ∈ Q * Q') hw ?_ ?_
  · intro p hp q hq
    rw [map_mul]
    exact Submodule.mul_mem_mul (h p hp) (h' q hq)
  · intro u v hu hv
    rw [map_add]
    exact add_mem hu hv
end PI.DIP.NormOne
