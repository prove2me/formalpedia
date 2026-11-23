-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.lemSJ_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:51.654228+00:00
-- url     : https://prove2.me/submissions/ca35156e-5043-43b3-8e12-fc13dfbdf639

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA

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
open scoped Matrix
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (x : EuclideanSpace ℂ ι) : (lemSJ : _ →ₗ[ℝ] _) x = (-I : ℂ) • x := rfl
end ReciprocityTheory.ChartRestriction.G.I2
