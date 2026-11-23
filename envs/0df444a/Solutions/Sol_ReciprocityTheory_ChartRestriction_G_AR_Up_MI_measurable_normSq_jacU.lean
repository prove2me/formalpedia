-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.measurable_normSq_jacU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:49.641579+00:00
-- url     : https://prove2.me/submissions/b2153658-ab94-4bd0-89ed-3d4ae3f3801d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_continuous_jacU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution : Measurable fun y : UpI ι r → ℂ => ENNReal.ofReal (Complex.normSq (jacU y)) :=
  (ENNReal.continuous_ofReal.comp (Complex.continuous_normSq.comp continuous_jacU)).measurable
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
