-- Prove2me | solution 1 for PI.FJMB.aeval_killS_union
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:03.63892+00:00
-- url     : https://prove2.me/submissions/71035f6d-ea69-4567-b9f0-0bc7188233a0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Theorems.Thm_P2M_PI_FJMB_aeval_aeval__e19064defd0d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}
namespace PI.FJMB
theorem _root_.solution (S T : Set σ) (f : MvPolynomial σ ℂ) :
    aeval (killS S) (aeval (killS T) f) = aeval (killS (S ∪ T)) f := by
  rw [aeval_aeval']
  congr 2
  funext v
  by_cases hT : v ∈ T
  · simp [killS, hT]
  · by_cases hS : v ∈ S <;> simp [killS, hT, hS]
end PI.FJMB
