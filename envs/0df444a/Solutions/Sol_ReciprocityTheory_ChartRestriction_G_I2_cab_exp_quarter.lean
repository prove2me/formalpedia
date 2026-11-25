-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.cab_exp_quarter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:10:14.043833+00:00
-- url     : https://prove2.me/submissions/81ed7238-762a-46a1-ba92-14ff129ba7fe

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
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution : (1.28 : ℝ) ≤ Real.exp (1 / 4) := by
  have := Real.quadratic_le_exp_of_nonneg (x := 1 / 4) (by norm_num)
  norm_num at this ⊢; linarith
end ReciprocityTheory.ChartRestriction.G.I2
