-- Prove2me | solution 1 for PI.ScRefExists.Id.evA_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:19:32.036599+00:00
-- url     : https://prove2.me/submissions/0a5258cb-2f77-4f70-b26b-f3b8edc1733b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemLiftOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemAd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open PI PI.ScRefExists PI.ScRefExists.Id
variable {F : Type} [Field F] [NumberField F]
namespace PI.ScRefExists.Id
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (a : Af F) : evA v a = a v := rfl
end PI.ScRefExists.Id
