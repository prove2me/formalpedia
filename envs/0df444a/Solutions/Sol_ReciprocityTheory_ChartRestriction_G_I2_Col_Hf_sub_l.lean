-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.Hf_sub_l
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:11.272684+00:00
-- url     : https://prove2.me/submissions/2a721f13-b1ee-4e08-b64b-ebd4075173a8

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
theorem _root_.solution (v v' w : EuclideanSpace ℂ ι) : Hf (v - v') w = Hf v w - Hf v' w := by
  simp only [Hf, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
end ReciprocityTheory.ChartRestriction.G.I2.Col
