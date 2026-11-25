-- Prove2me | solution 1 for PI.VolStabW.FiniteFieldSplitting.ffH_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:57:02.505254+00:00
-- url     : https://prove2.me/submissions/204d4598-4ddf-445d-8796-531569d4f812

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k] {M a : ℕ}
namespace PI.VolStabW.FiniteFieldSplitting
theorem _root_.solution (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).1 = ∑ i, ∑ j, (x i).2 * (J i j).1 * (y j).1 := by
  simp [ffH, Prod.fst_sum]
end PI.VolStabW.FiniteFieldSplitting
