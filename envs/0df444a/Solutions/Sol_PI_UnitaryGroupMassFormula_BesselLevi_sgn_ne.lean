-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BesselLevi.sgn_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:37:34.209699+00:00
-- url     : https://prove2.me/submissions/1a263f40-5777-466a-85bf-05b19a5eff53

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselLevi
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselLeviAction_MulVecBvecApply

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
theorem _root_.solution (i : Fin (2 * r + k + 1)) : sgn k r i ≠ 0 := by
  unfold sgn
  split_ifs <;> norm_num
end PI.UnitaryGroupMassFormula.BesselLevi
