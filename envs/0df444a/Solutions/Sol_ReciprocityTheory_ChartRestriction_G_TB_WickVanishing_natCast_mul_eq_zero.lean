-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.natCast_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:17.735825+00:00
-- url     : https://prove2.me/submissions/eeb99975-c2ca-4152-ac7d-6950139b3cd9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {x : k} {n : ℕ} (hn : n ≠ 0) (h : (n : k) * x = 0) : x = 0 := by
  have hu : IsUnit (n : k) := by
    rw [← map_natCast (algebraMap ℚ k)]
    exact (IsUnit.mk0 _ (by exact_mod_cast hn)).map _
  exact hu.mul_right_eq_zero.mp h
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
