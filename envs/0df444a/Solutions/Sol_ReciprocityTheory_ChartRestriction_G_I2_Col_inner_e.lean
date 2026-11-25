-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.inner_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:41.809424+00:00
-- url     : https://prove2.me/submissions/ca2adc9f-63da-4870-a971-43ffc612adc6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
open scoped InnerProductSpace
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.Col
variable {ι : Type} [Fintype ι]
variable (K : Submodule ℝ (EuclideanSpace ℂ ι))
namespace ReciprocityTheory.ChartRestriction.G.I2.Col
theorem _root_.solution (k l : Fin (dK K)) : ⟪e K k, e K l⟫_ℝ = if k = l then 1 else 0 := by
  show ⟪((ob K k : K) : EuclideanSpace ℂ ι), ((ob K l : K) : EuclideanSpace ℂ ι)⟫_ℝ = _
  rw [← Submodule.coe_inner]
  exact orthonormal_iff_ite.1 (ob K).orthonormal k l
end ReciprocityTheory.ChartRestriction.G.I2.Col
