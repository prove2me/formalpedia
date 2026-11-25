-- Prove2me | solution 1 for P2M_PI_OmVe_ffH_snd__84f5c783313d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:29:12.80263+00:00
-- url     : https://prove2.me/submissions/03b3333f-8859-404b-844b-f2a3ff7d44b0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_CountGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_FfHSelfOfSnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmVe
open PI.VolStabSW Matrix
variable {k : Type} [Field k] {M : ℕ} (J : Matrix (Fin M) (Fin M) (k × k))
namespace PI.OmVe
theorem _root_.solution (y x : Fin M → k × k) :
    (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J y x).2 = ∑ i, ∑ l, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (y i) * J i l).2 * (x l).2 := by
  simp only [ffH, Prod.snd_sum, Prod.snd_mul]
end PI.OmVe
