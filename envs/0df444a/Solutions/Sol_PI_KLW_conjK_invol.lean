-- Prove2me | solution 1 for PI.KLW.conjK_invol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:07:20.996465+00:00
-- url     : https://prove2.me/submissions/7fdb426d-cbb2-4d8c-b150-a808398dc617

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType
import Theorems.Thm_PI_KLW_conjK_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
namespace PI.KLW
theorem _root_.solution (cj : E ≃ₐ[ℚ] E) (hc : PI.KerIso.IsConj K cj) (k : K) :
    conjK cj hc.2.1 (conjK cj hc.2.1 k) = k :=
  (algebraMap K E).injective (by rw [conjK_spec, conjK_spec, hc.1])
end PI.KLW
