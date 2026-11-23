-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimB.continuous_rl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:47.843801+00:00
-- url     : https://prove2.me/submissions/fe121402-4a51-4f9e-81c2-bd9f613fe609

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Complex
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.DimB
variable {k : ℕ}
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_11
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_13
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_16
namespace ReciprocityTheory.ChartRestriction.G.I2.DimB
theorem _root_.solution : Continuous (rl (k := k)) :=
  continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
end ReciprocityTheory.ChartRestriction.G.I2.DimB
