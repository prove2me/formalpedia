-- Prove2me | solution 1 for PI.VolStabSW.FiniteFieldSplitting.ffH_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:01:05.994356+00:00
-- url     : https://prove2.me/submissions/c15d95e4-1ebc-4dff-b2c8-241f8c8a2885

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
    (ffH (swapR k) J x y).1 = ∑ i, ∑ j, (x i).2 * (J i j).1 * (y j).1 := by
  unfold ffH
  simp [Prod.fst_sum, swapR]
end PI.VolStabSW.FiniteFieldSplitting
