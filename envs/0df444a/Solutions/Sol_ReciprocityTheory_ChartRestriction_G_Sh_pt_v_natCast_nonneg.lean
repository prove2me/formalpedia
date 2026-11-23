-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt_v_natCast_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:11.329413+00:00
-- url     : https://prove2.me/submissions/ce67d777-7f96-4a20-9e65-cf5de25cd766

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution (n : ℕ) : (0 : WithTop ℝ) ≤ v (n : C) := by
  induction n with
  | zero => rw [Nat.cast_zero, v.map_zero]; exact le_top
  | succ n ih =>
    rw [Nat.cast_succ]
    exact le_trans (le_min ih (by rw [v.map_one])) (v.map_add _ _)
end ReciprocityTheory.ChartRestriction.G.Sh
