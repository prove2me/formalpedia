-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.KerSelfDual.one_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:41.646806+00:00
-- url     : https://prove2.me/submissions/987fbd34-faf8-434e-be0d-39322b35c99e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualOfDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualDifferent_Imports
import Theorems.Thm_PI_UnitaryGroupMassFormula_KerSelfDual_int_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.KerSelfDual
namespace PI.UnitaryGroupMassFormula.KerSelfDual
theorem _root_.solution {E : Type} [Field E] [NumberField E] (cj : E ≃ₐ[ℚ] E) {z : E}
    (hz : z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) :
    cj z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
  rw [FractionalIdeal.mem_one_iff] at hz ⊢
  obtain ⟨x, rfl⟩ := hz
  exact int_map cj x
end PI.UnitaryGroupMassFormula.KerSelfDual
