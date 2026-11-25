-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.rhoSq_ins_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:25:14.883735+00:00
-- url     : https://prove2.me/submissions/0da8e22b-8b55-44ad-ad21-67736d3073dc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_Lsq_ins
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_sumR_ins_succ

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
    rhoSq (ins y z) i.succ = rhoSq (tailPt y) i.succ := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq
  rw [Lsq_ins, sumR_ins_succ]
  all_goals rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
