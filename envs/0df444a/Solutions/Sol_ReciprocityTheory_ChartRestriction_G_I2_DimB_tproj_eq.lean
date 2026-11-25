-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimB.tproj_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:08:00.633794+00:00
-- url     : https://prove2.me/submissions/94ab61d4-1d8f-40c2-8b52-03978bc46342

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
theorem _root_.solution {s t : Fin k → ℝ} (h : tproj s = tproj t) :
    ∃ n : Fin k → ℤ, t = s + fun i => (n i : ℝ) := by
  have hi : ∀ i, ∃ m : ℤ, t i = s i + m := by
    intro i
    have h1 : ((s i : ℝ) : UnitAddCircle) = (t i : UnitAddCircle) := congrFun h i
    have h2 : (((t i - s i : ℝ)) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, h1, sub_self]
    obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h2
    refine ⟨m, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hm
    linarith
  choose n hn using hi
  exact ⟨n, funext fun i => by simp [hn i]⟩
end ReciprocityTheory.ChartRestriction.G.I2.DimB
