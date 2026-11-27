-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qf30_aux3__19f76c723558
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:14:35.53083+00:00
-- url     : https://prove2.me/submissions/0e059537-1ac9-4da1-aae5-de2edefa62f5

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsotypicStableUnderOperators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qf30
theorem _root_.solution.{u_1, u_2} :
    ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],
      SMulCommClass K K V := by
  intro K V _ _ _
  exact ⟨fun r s x => by rw [smul_smul, smul_smul, mul_comm]⟩
end UpperTheory.Reformulated.B.Qf30
