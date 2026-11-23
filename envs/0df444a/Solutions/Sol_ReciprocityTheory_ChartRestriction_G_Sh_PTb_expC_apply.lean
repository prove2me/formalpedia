-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.expC_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:26.988371+00:00
-- url     : https://prove2.me/submissions/ac2d1ce6-a168-4b2b-acdf-1c97108228ee

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
theorem _root_.solution {q : ℕ} (hq : q ≠ 0) (ga : Fin d → PowerSeries C) (a : Fin d) :
    expC q ga a = PowerSeries.expand q hq (ga a) := by
  first
  | rfl
  | (simp only [expC]; rw [PowerSeries.expand_eq_subst])
  | (unfold expC; ext m; rw [PowerSeries.coeff_expand, PowerSeries.coeff_subst_X_pow] <;> simp [hq])
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
