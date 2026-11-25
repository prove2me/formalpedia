-- Prove2me | solution 1 for PI.QnLevBasicsW.herm_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:33:42.597089+00:00
-- url     : https://prove2.me/submissions/79181822-7507-44d1-a204-a37fbabc4856

import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Theorems.Thm_PI_QnLevBasicsW_blocks_mulVec_lift
import Theorems.Thm_PI_QnLevBasicsW_dot_lift
import Theorems.Thm_PI_QnLevBasicsW_Hpk_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QnLevBasicsW
open Formalism.QuantumDeterminants
variable {k i r' : ℕ}
namespace PI.QnLevBasicsW
theorem _root_.solution (v w : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (i + r')) (liftVec k i r' v) (liftVec k i r' w) = herm (Hpk k r') v w := by
  unfold herm
  rw [Hpk_eq, blocks_mulVec_lift, dot_lift]
end PI.QnLevBasicsW
