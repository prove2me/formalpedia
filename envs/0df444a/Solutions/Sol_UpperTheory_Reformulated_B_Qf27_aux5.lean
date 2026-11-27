-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qf27.aux5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:33:32.71685+00:00
-- url     : https://prove2.me/submissions/23eacc3f-bbab-4d66-a940-4ce5db4c534f

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InfEmbUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qf27
theorem _root_.solution :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E], IsScalarTower F E E := by
  intro F E _ _ _
  infer_instance
end UpperTheory.Reformulated.B.Qf27
