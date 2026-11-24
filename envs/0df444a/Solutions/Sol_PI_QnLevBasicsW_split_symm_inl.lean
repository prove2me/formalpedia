-- Prove2me | solution 1 for PI.QnLevBasicsW.split_symm_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:16:38.792778+00:00
-- url     : https://prove2.me/submissions/e0a5c2f5-882c-426c-b0f1-63b59e643daa

import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective

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
theorem _root_.solution (a : Fin (2 * r' + k + 1)) :
    ((split k i r').symm (Sum.inl a)).val = a.val + i := rfl
end PI.QnLevBasicsW
