-- Prove2me | solution 1 for PI.LocalEndW.valContinuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:50:57.530875+00:00
-- url     : https://prove2.me/submissions/32811111-20af-490b-ac30-207afa79ea70

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_IsUniformInducingOfVal
import Theorems.Thm_PI_LocalEndW_isUniformInducing_of_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Uniformity
open PI PI.LocalEndW
namespace PI.LocalEndW
theorem _root_.solution : ValContinuous := fun _ _ _ _ τ hτ => (isUniformInducing_of_val τ hτ).uniformContinuous.continuous
end PI.LocalEndW
