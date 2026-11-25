-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.sum_smul_tangent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:28:10.768333+00:00
-- url     : https://prove2.me/submissions/13eb10e0-f59c-4495-bbbf-c6a363efbb19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_EqZeroOfVecMulTmat

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
theorem _root_.solution (γ : Fin d → Fin d → PowerSeries C) (x : Fin d → C) :
    ∑ b, x b • tangent (γ b) = Matrix.vecMul x (tmat γ) := by
  funext c
  simp [Matrix.vecMul, dotProduct, tmat, Finset.sum_apply]
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
