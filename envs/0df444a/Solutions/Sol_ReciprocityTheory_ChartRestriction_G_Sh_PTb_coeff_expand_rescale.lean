-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.coeff_expand_rescale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:52.029141+00:00
-- url     : https://prove2.me/submissions/2ed352ac-c03a-48de-97f1-13071481d9e4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution (q : ℕ) (hq : q ≠ 0) (x : C) (f : PowerSeries C) (m : ℕ) :
    PowerSeries.coeff m (PowerSeries.expand q hq (PowerSeries.rescale x f)) =
      if q ∣ m then x ^ (m / q) * PowerSeries.coeff (m / q) f else 0 := by
  rw [PowerSeries.coeff_expand]
  split_ifs
  · rw [PowerSeries.coeff_rescale]
  · rfl
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
