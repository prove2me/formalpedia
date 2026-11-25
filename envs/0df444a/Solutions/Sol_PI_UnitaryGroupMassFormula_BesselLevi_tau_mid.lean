-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BesselLevi.tau_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:37:41.545587+00:00
-- url     : https://prove2.me/submissions/181d58ba-822c-4eaa-bc54-481955002075

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselLevi
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselLeviAction_MulVecBvecApply
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_tau_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BesselLevi
variable {k r : ℕ}
namespace PI.UnitaryGroupMassFormula.BesselLevi
theorem _root_.solution (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val ∧ i.val ≤ r + k) : tau k r i = i := by
  exact Fin.ext (by rw [tau_val, if_neg (by omega)])
end PI.UnitaryGroupMassFormula.BesselLevi
