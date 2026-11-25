-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.tailFin_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:56:30.976062+00:00
-- url     : https://prove2.me/submissions/2ef0f12b-000d-4c83-8031-bddb3e40fa58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_CriticalExponentSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailFinOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_kc_lt_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_tail_eq


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
namespace ReciprocityTheory.ChartRestriction.DS.Xi
theorem _root_.solution (hCH : CH) : TailFin := by
  intro p m α ν hc hpos
  rw [J2.tail_eq]
  exact ENNReal.mul_lt_top (J2.kc_lt_top (by linarith)) (hCH p m _ hc)
end ReciprocityTheory.ChartRestriction.DS.Xi
