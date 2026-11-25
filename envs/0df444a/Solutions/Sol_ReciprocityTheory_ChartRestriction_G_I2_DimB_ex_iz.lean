-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimB.ex_iz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:08:12.684026+00:00
-- url     : https://prove2.me/submissions/ddfc48d1-36fc-4afd-8688-71f7476e4381

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
theorem _root_.solution (m n : Fin k → ℤ) : ex m (iz n) = 1 := by
  simp only [ex, iz]
  have : ∑ l, (m l : ℂ) * (n l : ℂ) = ((∑ l, m l * n l : ℤ) : ℂ) := by push_cast; rfl
  rw [this, show -(2 * Real.pi * I * ((∑ l, m l * n l : ℤ) : ℂ)) =
    ((-(∑ l, m l * n l) : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I _
end ReciprocityTheory.ChartRestriction.G.I2.DimB
