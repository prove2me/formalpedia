-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qk30_aux3__df6134d3b073
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:19:44.136037+00:00
-- url     : https://prove2.me/submissions/7828a88b-6a5c-430d-b447-cb321af173cc

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HwvLoweringSpanLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qk30
theorem _root_.solution.{u_1, u_2} :
    ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],
      SMulCommClass K K V := by
  intro K V _ _ _
  infer_instance
end UpperTheory.Reformulated.B.Qk30
