-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.bco_ins_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:13.618911+00:00
-- url     : https://prove2.me/submissions/92a6c4cf-f1e1-4b4a-a1e5-cd6367fcecbc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_sum_ins_succ

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
    bco (ins y z) i.succ = bco (tailPt y) i.succ := by
  have h : (∑ j : Fin (p + 1), if i.succ.val ≤ j.val then (ins y z).2.1 j * star ((ins y z).1 j) else 0) =
      ∑ j : Fin (p + 1), if i.succ.val ≤ j.val then (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y).2.1 j * star ((ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y).1 j) else 0 :=
    sum_ins_succ y z i (fun a b => a * star b)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.bco
  rw [h]
  all_goals rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
