-- Prove2me | solution 1 for PI.FJMB.aeval_killS_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:34.91519+00:00
-- url     : https://prove2.me/submissions/850cb5fa-9ea8-48dd-be33-cc0f0d32c183

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim

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
theorem _root_.solution (f : MvPolynomial σ ℂ) : aeval (killS (∅ : Set σ)) f = f := by
  have : killS (∅ : Set σ) = X := by funext v; simp [killS]
  rw [this, aeval_X_left_apply]
end PI.FJMB
