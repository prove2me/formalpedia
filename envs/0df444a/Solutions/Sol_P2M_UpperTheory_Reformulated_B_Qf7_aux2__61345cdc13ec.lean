-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qf7_aux2__61345cdc13ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:14:37.562875+00:00
-- url     : https://prove2.me/submissions/a8de48e9-d552-4f66-b6f7-17416f3e5bbb

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WeightComponentsMemInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qf7
theorem _root_.solution.{u_1, u_2} :
    ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],
      SMulCommClass K K V := by
  intro K V _ _ _
  infer_instance
end UpperTheory.Reformulated.B.Qf7
