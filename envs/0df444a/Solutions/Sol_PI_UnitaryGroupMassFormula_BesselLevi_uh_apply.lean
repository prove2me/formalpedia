-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BesselLevi.uh_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:37:45.407558+00:00
-- url     : https://prove2.me/submissions/73676f6b-4746-437c-bb99-4e0adad8a98b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselLevi
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselLeviAction_MulVecBvecApply
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_mul_hpk_apply
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_sgn_tau
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_tau_tau


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
theorem _root_.solution (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) :
    (Aᴴ * Hpk k r * A) i j = ∑ p, star (A p i) * (sgn k r p * A (tau k r p) j) := by
  rw [Matrix.mul_apply]
  simp only [mul_hpk_apply, Matrix.conjTranspose_apply]
  refine Fintype.sum_equiv (Function.Involutive.toPerm (tau k r) tau_tau)
    (fun p => star (A (tau k r p) i) * sgn k r p * A p j)
    (fun p => star (A p i) * (sgn k r p * A (tau k r p) j)) (fun p => ?_)
  show _ = star (A (tau k r p) i) * (sgn k r (tau k r p) * A (tau k r (tau k r p)) j)
  rw [tau_tau, sgn_tau]
  ring
end PI.UnitaryGroupMassFormula.BesselLevi
