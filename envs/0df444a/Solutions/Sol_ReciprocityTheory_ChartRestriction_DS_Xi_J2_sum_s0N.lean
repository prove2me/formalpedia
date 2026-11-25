-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.sum_s0N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:18:27.015117+00:00
-- url     : https://prove2.me/submissions/a2424e56-c8e0-43c3-9112-1d532b7a8ac9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_CriticalExponentSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution (p m : ℕ) : ∑ i, s0N p m i = 2 * p + m + 1 := by
  rw [Fin.sum_univ_castSucc]
  simp [s0N]
  ring
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
