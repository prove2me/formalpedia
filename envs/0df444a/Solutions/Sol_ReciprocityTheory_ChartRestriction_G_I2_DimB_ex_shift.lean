-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimB.ex_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:08.055862+00:00
-- url     : https://prove2.me/submissions/80e01970-3a05-4c66-9452-df70c4322be5

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
theorem _root_.solution (m : Fin k → ℤ) (q : ℕ) (j : Fin k) (z : Fin k → ℂ) :
    cexp (2 * Real.pi * I * q * z j) * ex m z = ex (m - (q : ℤ) • Pi.single j 1) z := by
  simp only [ex, ← Complex.exp_add]
  congr 1
  have : ∑ l, (((m - (q : ℤ) • (Pi.single j 1 : Fin k → ℤ)) l : ℤ) : ℂ) * z l = ∑ l, (m l : ℂ) * z l - q * z j := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul, sub_mul,
      Finset.sum_sub_distrib]
    congr 1
    simp [Pi.single_apply]
  rw [this]; ring
end ReciprocityTheory.ChartRestriction.G.I2.DimB
