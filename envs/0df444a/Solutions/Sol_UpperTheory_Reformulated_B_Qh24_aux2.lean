-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qh24.aux2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:33:37.318688+00:00
-- url     : https://prove2.me/submissions/9d0d17be-bb32-4746-9235-74087ee00e7d

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InclR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qh24
theorem _root_.solution :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
      SubsemiringClass (ValuationSubring (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v))
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v) := by
  intros
  infer_instance
end UpperTheory.Reformulated.B.Qh24
