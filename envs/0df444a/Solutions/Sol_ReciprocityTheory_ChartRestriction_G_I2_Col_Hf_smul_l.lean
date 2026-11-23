-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.Hf_smul_l
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:10.929014+00:00
-- url     : https://prove2.me/submissions/3975d1a0-d74c-48bc-9c44-0cc7c9e0c58c

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
namespace ReciprocityTheory.ChartRestriction.G.I2.Col
theorem _root_.solution (c : ℂ) (v w : EuclideanSpace ℂ ι) : Hf (c • v) w = c * Hf v w := by
  simp only [Hf, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
end ReciprocityTheory.ChartRestriction.G.I2.Col
