-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.luD_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:14.33619+00:00
-- url     : https://prove2.me/submissions/ae6e94ba-851e-443a-8c03-f1b9321f88f8

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
theorem _root_.solution (w h : Ix ι r → ℂ) (i : Ix ι r) :
    luD w h i = ∑ k, sl h i.1 i.2.1 k * up w i.1 k i.2.2 + ∑ k, (1 + sl w i.1) i.2.1 k * up h i.1 k i.2.2 := by
  show (sl h i.1 * up w i.1 + (1 + sl w i.1) * up h i.1) i.2.1 i.2.2 = _
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
