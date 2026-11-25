-- Prove2me | solution 1 for PI.VolStabSW.FiniteFieldSplitting.ffH_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:53:34.950801+00:00
-- url     : https://prove2.me/submissions/7fb2d499-8f8e-4243-bce1-5c721401086e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k] {M a : ℕ}
namespace PI.VolStabSW.FiniteFieldSplitting
theorem _root_.solution (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).2 = ∑ i, ∑ j, (x i).1 * (J i j).2 * (y j).2 := by
  unfold ffH
  simp [Prod.snd_sum, swapR]
end PI.VolStabSW.FiniteFieldSplitting
