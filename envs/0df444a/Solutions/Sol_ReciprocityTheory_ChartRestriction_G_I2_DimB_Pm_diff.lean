-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimB.Pm_diff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:00.844144+00:00
-- url     : https://prove2.me/submissions/ae1de1f7-8947-4305-bf7f-9ee70a97fdb9

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
theorem _root_.solution (h : (Fin k → ℂ) → ℂ) (hd : Differentiable ℂ h) (m : Fin k → ℤ) :
    Differentiable ℂ (Pm h m) := by
  unfold Pm ex; fun_prop
end ReciprocityTheory.ChartRestriction.G.I2.DimB
