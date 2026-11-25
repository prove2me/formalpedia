-- Prove2me | solution 1 for PI.ScRefExists.Id.natCast_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:20:50.135404+00:00
-- url     : https://prove2.me/submissions/d09f75d5-6043-4c38-b1fd-a0c620b98977

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) :
    Valued.v ((g : ℕ) : v.adicCompletion F) ≤ 1 := memO.1 (natCast_mem _ g)
end PI.ScRefExists.Id
