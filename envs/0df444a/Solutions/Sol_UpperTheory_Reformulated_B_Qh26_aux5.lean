-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qh26.aux5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:33:57.501802+00:00
-- url     : https://prove2.me/submissions/591d1e77-a152-4a9a-81b0-92744cfb302b

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
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E], IsScalarTower F E E := by
  intros; infer_instance
end UpperTheory.Reformulated.B.Qh26
