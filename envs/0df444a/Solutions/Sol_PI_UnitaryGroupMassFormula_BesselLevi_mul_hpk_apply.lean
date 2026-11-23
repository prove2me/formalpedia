-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BesselLevi.mul_hpk_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:59.176798+00:00
-- url     : https://prove2.me/submissions/4b729d2c-45ae-498a-96c4-da9f7c3d18aa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselLevi
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselLeviAction_MulVecBvecApply
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_mul_apply
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
    (i j : Fin (2 * r + k + 1)) : (A * Hpk k r) i j = A i (tau k r j) * sgn k r j := by
  have hH : ∀ l, Hpk k r l j = sgn k r l * (if tau k r l = j then 1 else 0) := fun l => by
    have e := hpk_mul_apply (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) l j
    rw [Matrix.mul_one, Matrix.one_apply] at e
    exact e
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r j)]
  · rw [hH, tau_tau, if_pos rfl, mul_one, sgn_tau]
  · intro l _ hl
    rw [hH, if_neg (fun h => hl (by rw [← h, tau_tau])), mul_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
end PI.UnitaryGroupMassFormula.BesselLevi
