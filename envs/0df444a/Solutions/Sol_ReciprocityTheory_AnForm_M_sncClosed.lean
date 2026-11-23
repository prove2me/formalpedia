-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.sncClosed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:34.853491+00:00
-- url     : https://prove2.me/submissions/04427b03-3208-44e6-bfb0-bcaaf5384ea5

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_SNCAtlas
import Theorems.Thm_ReciprocityTheory_AnForm_M_SimpleNormalCrossingSliceCharts_isClosed_divisorComponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Topology Filter Set
open scoped ContDiff
noncomputable section
open SimpleNormalCrossingSliceCharts
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : SNCClosedStatement := by
  unfold SNCClosedStatement
  intro e X _ A L s r m W h k
  exact isClosed_divisorComponent A L s m W h k
end ReciprocityTheory.AnForm.M
