-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.one_add_sl_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:42.682909+00:00
-- url     : https://prove2.me/submissions/85e4db75-0f39-4e1b-b0dd-23acee387f66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution (w : Ix ι r → ℂ) (τ : ι) {a k : Fin r} (h : a < k) : (1 + sl w τ) a k = 0 := by
  rw [Matrix.add_apply, Matrix.one_apply_ne h.ne]
  simp [sl, not_lt.mpr h.le]
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
