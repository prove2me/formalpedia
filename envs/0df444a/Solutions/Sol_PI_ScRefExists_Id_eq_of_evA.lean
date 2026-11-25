-- Prove2me | solution 1 for PI.ScRefExists.Id.eq_of_evA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:25:19.047428+00:00
-- url     : https://prove2.me/submissions/a403f0ed-471b-40cd-8dcf-a2ea1a55668b

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
theorem _root_.solution {a b : Af F} (h : ∀ v, evA v a = evA v b) : a = b := by
  first
    | (ext v; exact h v)
    | exact Subtype.ext (funext h)
    | exact RestrictedProduct.ext h
end PI.ScRefExists.Id
