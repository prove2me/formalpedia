-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qk24.aux2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:34:06.995441+00:00
-- url     : https://prove2.me/submissions/db232ca0-035b-4a97-8138-cbb21bf0647f

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SignActionMapComm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qk24
theorem _root_.solution :
    ∀ (I : Formalism.MainNotions.S.AutInst), IsFractionRing (NumberField.RingOfIntegers I.F) I.F := by
  intro I
  infer_instance
end UpperTheory.Reformulated.B.Qk24
