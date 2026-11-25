-- Prove2me | solution 1 for PI.ExpIntWProof.norm_intCast_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:17.672608+00:00
-- url     : https://prove2.me/submissions/f1bd360e-3db5-43dc-8492-a17b8c4ecb96

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
theorem _root_.solution (p : ℕ) [Fact p.Prime] (t : ℤ) : ‖(t : ℂ_[p])‖ ≤ 1 := by
  exact IsUltrametricDist.norm_intCast_le_one ℂ_[p] t
end PI.ExpIntWProof
