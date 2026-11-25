-- Prove2me | solution 1 for PI.WAU.B.countable_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:50.3897+00:00
-- url     : https://prove2.me/submissions/fe06e0bb-9aee-48f8-8328-39a83b8ffe55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU PI.WAU.B
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]
namespace PI.WAU.B
theorem _root_.solution (K : Type) [Field K] [NumberField K] : Countable K := by
  exact (Module.finBasis ℚ K).equivFun.injective.countable
end PI.WAU.B
