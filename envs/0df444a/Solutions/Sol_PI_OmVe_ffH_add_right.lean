-- Prove2me | solution 1 for PI.OmVe.ffH_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:03:34.930799+00:00
-- url     : https://prove2.me/submissions/ed481690-534f-427c-9eed-36d70ef9adc1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_SingleMulVec

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
variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
namespace PI.OmVe
theorem _root_.solution (x y z : Fin M → K) : ffH σ J x (y + z) = ffH σ J x y + ffH σ J x z := by
  simp [ffH, mul_add, Finset.sum_add_distrib]
end PI.OmVe
