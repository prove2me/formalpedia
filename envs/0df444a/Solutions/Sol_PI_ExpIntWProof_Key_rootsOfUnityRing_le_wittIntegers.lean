-- Prove2me | solution 1 for PI.ExpIntWProof.Key.rootsOfUnityRing_le_wittIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:37:58.180828+00:00
-- url     : https://prove2.me/submissions/e0b93386-d717-4746-95a5-47dd54fd2d82

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_RootsOfUnityRingLeWittIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof PI.ExpIntWProof.Key
namespace PI.ExpIntWProof.Key
theorem _root_.solution (p : ℕ) [Fact p.Prime] : S0 p ≤ Wp p := Subring.le_topologicalClosure _
end PI.ExpIntWProof.Key
