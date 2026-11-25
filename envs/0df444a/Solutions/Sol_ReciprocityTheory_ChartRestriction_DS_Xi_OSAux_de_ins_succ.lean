-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.de_ins_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:50:19.755676+00:00
-- url     : https://prove2.me/submissions/2087a8fd-22b7-40c0-aaa4-4789a383e49a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_Lsq_ins
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_rhoSq_ins_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_bco_ins_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) :
    de (ins y z) i.succ = de (tailPt y) i.succ := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.de
  rw [Lsq_ins, rhoSq_ins_succ, bco_ins_succ]
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
