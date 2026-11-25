-- Prove2me | solution 1 for PI.LocGlobInclWork.maximal_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:50:42.164635+00:00
-- url     : https://prove2.me/submissions/a499cd98-6781-4332-84b6-6fc66dc8d9d6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocGlobIncl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalInclusion_SmulMemIdealSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.LocGlobInclWork
variable {K : Type} [Field K] [NumberField K]
namespace PI.LocGlobInclWork
theorem _root_.solution (m : Ideal (𝓞 K)) (hm : m.IsMaximal) : m ≠ ⊥ := by
  haveI := hm
  exact (Ideal.bot_lt_of_maximal m (NumberField.RingOfIntegers.not_isField K)).ne'
end PI.LocGlobInclWork
