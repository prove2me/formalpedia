-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.vecMul_one_add_smul_vecMulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:28.194326+00:00
-- url     : https://prove2.me/submissions/9a2d6d9a-aede-4901-aaa7-03ca7962a35f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open Matrix
variable {R : Type} [CommRing R] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution (p q y : Fin n → R) (c : R) :
    y ᵥ* (1 + c • vecMulVec p q) = y + (c * (y ⬝ᵥ p)) • q := by
  rw [Matrix.vecMul_add, Matrix.vecMul_one]
  ext j
  simp only [Pi.add_apply, add_right_inj, Matrix.vecMul, dotProduct, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  all_goals exact Finset.sum_congr rfl (fun i _ => by ring)
end PI.UnitaryGroupMassFormula.ScXuExists
