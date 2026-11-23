-- Prove2me | solution 1 for PI.ExpIntWProof.Key.isClosed_Wp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:17.206824+00:00
-- url     : https://prove2.me/submissions/9b909f48-0f36-46e0-a6aa-f6cfa4e96212

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
theorem _root_.solution (p : ℕ) [Fact p.Prime] : IsClosed (Wp p : Set ℂ_[p]) :=
  Subring.isClosed_topologicalClosure _
end PI.ExpIntWProof.Key
