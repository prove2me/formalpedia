-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimB.mF_tproj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:01.212749+00:00
-- url     : https://prove2.me/submissions/575753c3-baeb-462b-9139-848a75010160

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
theorem _root_.solution (m : Fin k → ℤ) (x : Fin k → ℝ) :
    UnitAddTorus.mFourier m (tproj x) = cexp (2 * Real.pi * I * ∑ l, (m l : ℂ) * (x l : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, tproj, fourier_coe_apply]
  rw [← Complex.exp_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp; ring
end ReciprocityTheory.ChartRestriction.G.I2.DimB
