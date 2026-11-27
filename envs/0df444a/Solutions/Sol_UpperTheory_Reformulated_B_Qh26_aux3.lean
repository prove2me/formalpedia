-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qh26.aux3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:33:47.409841+00:00
-- url     : https://prove2.me/submissions/789c174d-2d00-4619-98d2-df4ab5a20a60

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsInfEmbUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qh26
theorem _root_.solution :
    ∀ {F : Type} [inst : Field F], IsScalarTower F (UpperTheory.Reformulated.B.Qh26.Ainf F) (UpperTheory.Reformulated.B.Qh26.Ainf F) := by
  intros; infer_instance
end UpperTheory.Reformulated.B.Qh26
