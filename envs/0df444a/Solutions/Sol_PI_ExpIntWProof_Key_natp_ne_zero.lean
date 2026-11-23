-- Prove2me | solution 1 for PI.ExpIntWProof.Key.natp_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:23.35183+00:00
-- url     : https://prove2.me/submissions/65894d6e-8179-4d9d-9c54-1533f87d9181

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
variable {p : ℕ} [hp : Fact p.Prime]
namespace PI.ExpIntWProof.Key
theorem _root_.solution : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
end PI.ExpIntWProof.Key
