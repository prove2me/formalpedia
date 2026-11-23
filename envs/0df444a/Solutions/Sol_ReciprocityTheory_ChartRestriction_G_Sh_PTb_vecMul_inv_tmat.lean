-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.vecMul_inv_tmat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:49.038077+00:00
-- url     : https://prove2.me/submissions/e0076b5a-b8b2-45a3-8061-5c3d30a8252c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_EqZeroOfVecMulTmat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_tmat_isUnit_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution {γ : Fin d → Fin d → PowerSeries C} (hdet : v (tmat γ).det = 0)
    (w : Fin d → C) : Matrix.vecMul (Matrix.vecMul w (tmat γ)⁻¹) (tmat γ) = w := by
  rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (tmat_isUnit_det hdet), Matrix.vecMul_one]
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
