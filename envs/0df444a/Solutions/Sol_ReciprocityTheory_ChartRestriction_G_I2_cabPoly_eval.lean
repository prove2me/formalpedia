-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.cabPoly_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:02.283921+00:00
-- url     : https://prove2.me/submissions/2e58543b-c94e-4e5f-8808-50f030349233

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (η v : EuclideanSpace ℂ ι) (c : ℕ) :
    MvPolynomial.eval (fun i => v i) (cabPoly η c) = (Hf v η) ^ c := by
  unfold cabPoly Hf
  simp [mul_comm]
end ReciprocityTheory.ChartRestriction.G.I2
