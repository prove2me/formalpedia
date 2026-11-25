-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.eq_zero_of_vecMul_tmat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:28:47.508025+00:00
-- url     : https://prove2.me/submissions/bc02d8e4-2cc7-417e-a88f-68836403fdb7

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
    {x : Fin d → C} (h : Matrix.vecMul x (tmat γ) = 0) : x = 0 := by
  have h2 := congrArg (fun w => Matrix.vecMul w (tmat γ)⁻¹) h
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (tmat_isUnit_det hdet),
    Matrix.vecMul_one, Matrix.zero_vecMul] at h2
  exact h2
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
