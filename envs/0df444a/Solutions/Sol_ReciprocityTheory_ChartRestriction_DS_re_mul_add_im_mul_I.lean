-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.re_mul_add_im_mul_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:19.324933+00:00
-- url     : https://prove2.me/submissions/5531c3da-576a-46bd-bc40-710c83a28d02

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_ContDiffOnZeroOfContinuousOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (z c : ℂ) : (z.re : ℂ) * c + (z.im : ℂ) * (Complex.I * c) = c * z := by
  conv_rhs => rw [← Complex.re_add_im z]
  ring
end ReciprocityTheory.ChartRestriction.DS
