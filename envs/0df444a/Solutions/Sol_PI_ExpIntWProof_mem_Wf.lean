-- Prove2me | solution 1 for PI.ExpIntWProof.mem_Wf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:55:43.697057+00:00
-- url     : https://prove2.me/submissions/7c057bf0-fc38-44b5-8734-884ffcfa2482

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatCastMemWittIntegers
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatMemWf

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
theorem _root_.solution {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} : x ∈ Wf p ↔ InWf x := Iff.rfl
end PI.ExpIntWProof
