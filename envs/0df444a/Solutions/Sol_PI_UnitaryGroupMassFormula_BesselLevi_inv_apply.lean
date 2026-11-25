-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BesselLevi.inv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:37:28.926285+00:00
-- url     : https://prove2.me/submissions/da3eedee-217c-4c42-a1fd-f4c1b5204634

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselLevi
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselLeviAction_MulVecBvecApply
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_mul_hpk_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_inv_eq
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_mul_apply


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
theorem _root_.solution {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ UH (Hpk k r)) (p q : Fin (2 * r + k + 1)) :
    s⁻¹ p q = sgn k r p * (star (s (tau k r q) (tau k r p)) * sgn k r q) := by
  rw [inv_eq hs, mul_hpk_apply, hpk_mul_apply, Matrix.conjTranspose_apply]
  ring
end PI.UnitaryGroupMassFormula.BesselLevi
