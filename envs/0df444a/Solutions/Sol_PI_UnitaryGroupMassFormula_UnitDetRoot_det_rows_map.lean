-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.det_rows_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:38.347798+00:00
-- url     : https://prove2.me/submissions/56bd1072-8162-4430-ad6d-85b33befe635

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobVol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
variable (F : IntermediateField ℚ ℂ) {m : Type} [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (w : m → m → ℂ) :
    (Matrix.of fun j => δ (w j)).det = LinearMap.det δ * (Matrix.of w).det := by
  have h : Matrix.of (fun j => δ (w j)) = Matrix.of w * Matrix.transpose (LinearMap.toMatrix' δ) := by
    ext j i
    rw [Matrix.of_apply, ← LinearMap.toMatrix'_mulVec]
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  rw [h, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix', mul_comm]
end PI.UnitaryGroupMassFormula.UnitDetRoot
