-- Prove2me | solution 1 for PI.QnLevBasicsW.split_symm_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:12:36.985577+00:00
-- url     : https://prove2.me/submissions/45438212-ac2c-4d18-b8f3-0a76331431cd

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
theorem _root_.solution (b : Fin (2 * i)) :
    ((split k i r').symm (Sum.inr b)).val = if b.val < i then b.val else b.val + (2 * r' + k + 1) := rfl
end PI.QnLevBasicsW
