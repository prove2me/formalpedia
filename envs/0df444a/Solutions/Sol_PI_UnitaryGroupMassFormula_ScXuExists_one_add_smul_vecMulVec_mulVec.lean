-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.one_add_smul_vecMulVec_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:27.101891+00:00
-- url     : https://prove2.me/submissions/062eae03-51b5-4cd5-baf0-b0a57c88e7b8

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
theorem _root_.solution (p q x : Fin n → R) (c : R) :
    (1 + c • vecMulVec p q) *ᵥ x = x + (c * (q ⬝ᵥ x)) • p := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  ext i
  simp only [Pi.add_apply, add_right_inj, Matrix.mulVec, dotProduct, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  all_goals exact Finset.sum_congr rfl (fun j _ => by ring)
end PI.UnitaryGroupMassFormula.ScXuExists
