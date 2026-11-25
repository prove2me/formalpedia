-- Prove2me | solution 1 for PI.VolStabS.FiniteFieldSplitting.ffH_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:50:37.06546+00:00
-- url     : https://prove2.me/submissions/ca4bd270-2297-408d-97b8-712e70794315

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open PI.VolStabS.FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k] {M a : ℕ}
namespace PI.VolStabS.FiniteFieldSplitting
theorem _root_.solution (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).2 = ∑ i, ∑ j, (x i).1 * (J i j).2 * (y j).2 := by
  unfold ffH
  simp [Prod.snd_sum, swapR]
end PI.VolStabS.FiniteFieldSplitting
