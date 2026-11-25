-- Prove2me | solution 1 for PI.ExpIntWProof.p_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:21.893974+00:00
-- url     : https://prove2.me/submissions/84de50a6-6047-4b92-8e36-aaa4df18dc9c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatCastMemWittIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof
open PI
namespace PI.ExpIntWProof
theorem _root_.solution (p : ℕ) [Fact p.Prime] : (p : ℂ_[p]) ∈ Wp p := natCast_mem _ p
end PI.ExpIntWProof
