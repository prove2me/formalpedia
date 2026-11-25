-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimB.Pm_per
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:15:04.596482+00:00
-- url     : https://prove2.me/submissions/23b5a717-5dfc-4085-92a9-43950057ef89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_ex_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_ex_iz

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
theorem _root_.solution (h : (Fin k → ℂ) → ℂ) (hp : IPer h) (m : Fin k → ℤ) : IPer (Pm h m) :=
  fun n z => by simp only [Pm, ex_add, ex_iz, hp n z, mul_one]
end ReciprocityTheory.ChartRestriction.G.I2.DimB
