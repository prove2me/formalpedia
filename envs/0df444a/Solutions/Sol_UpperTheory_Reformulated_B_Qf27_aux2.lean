-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qf27.aux2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:33:19.046808+00:00
-- url     : https://prove2.me/submissions/51e13e43-f0a5-4584-961d-229c56377d3a

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
    ∀ {F : Type} [inst : Field F], SMulCommClass F (UpperTheory.Reformulated.B.Qf27.Ainf F) (UpperTheory.Reformulated.B.Qf27.Ainf F) := by
  intro F _
  infer_instance
end UpperTheory.Reformulated.B.Qf27
