-- Prove2me | solution 1 for P2M_PI_OmVe_ffH_fst__fe7b4dc579e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:29:10.754955+00:00
-- url     : https://prove2.me/submissions/019eaf12-0e37-48fb-9151-9d79fcdeccd6

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
    (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J y x).1 = ∑ i, ∑ l, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (y i) * J i l).1 * (x l).1 := by
  simp only [ffH, Prod.fst_sum, Prod.fst_mul]
end PI.OmVe
