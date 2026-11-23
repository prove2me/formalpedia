-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.sum_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:27.753097+00:00
-- url     : https://prove2.me/submissions/227bedf1-3d07-479c-a59e-838ed6c27c6b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_CriticalExponentSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailFinOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution {n : ℕ} (g : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    ∑ j ∈ Finset.Ioi l, g j = ∑ j, if l < j then g j else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
