-- Prove2me | solution 1 for PI.LocalEndW.val_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:51:06.043547+00:00
-- url     : https://prove2.me/submissions/127be7b1-451d-4596-adfa-35271b52206f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocalEnd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_IntVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain WithZero
open PI PI.LocalEndW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocalEndW
theorem _root_.solution (n : ℕ) :
    Valued.v ((n : v.adicCompletion F)) = v.intValuation (n : 𝓞 F) := by
  have h := v.valuedAdicCompletion_eq_valuation (K := F) (n : 𝓞 F)
  rw [HeightOneSpectrum.valuation_of_algebraMap] at h
  simpa using h
end PI.LocalEndW
