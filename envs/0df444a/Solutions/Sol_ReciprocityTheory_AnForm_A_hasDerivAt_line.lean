-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hasDerivAt_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:01.614619+00:00
-- url     : https://prove2.me/submissions/e72f7455-693b-41b2-935f-236f9d9b2c06

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (z w : E) (s : ℝ) : HasDerivAt (fun s : ℝ => z + s • w) w s := by
  simpa using ((hasDerivAt_id s).smul_const w).const_add z
end ReciprocityTheory.AnForm.A
