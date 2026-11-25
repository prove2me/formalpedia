-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimB.mF_ex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:45.153329+00:00
-- url     : https://prove2.me/submissions/3f737bed-7c42-4968-ac4f-bd654d0d6073

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_mF_tproj

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
    UnitAddTorus.mFourier (-m) (tproj x) = ex m (rl x) := by
  rw [mF_tproj, ex]
  congr 1
  simp only [rl, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  ring
end ReciprocityTheory.ChartRestriction.G.I2.DimB
