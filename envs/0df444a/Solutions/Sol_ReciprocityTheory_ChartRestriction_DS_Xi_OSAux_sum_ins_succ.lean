-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.sum_ins_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:27:55.879478+00:00
-- url     : https://prove2.me/submissions/99ba83b4-5290-46fb-a5d1-81933812f854

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux
private theorem ins_snd_fst_eq_tailPt_snd_fst_of_ne_zero {p m : ℕ} (y : Yp p m) (z : ℂ) {j : Fin (p + 1)} (hj : j ≠ 0) :
    (ins y z).2.1 j = (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y).2.1 j := by
  induction j using Fin.cases with
  | zero => exact absurd rfl hj
  | succ k => simp [ins, ReciprocityTheory.ChartRestriction.DS.Xi.tailPt]
end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) (g : ℂ → ℂ → ℂ) :
    (∑ j : Fin (p + 1), if i.succ.val ≤ j.val then g ((ins y z).2.1 j) ((ins y z).1 j) else 0) =
      ∑ j : Fin (p + 1), if i.succ.val ≤ j.val then g ((tailPt y).2.1 j) ((tailPt y).1 j) else 0 := by
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : i.succ.val ≤ j.val
  · have hj : j ≠ 0 := by
      rintro rfl
      simp at h
    rw [if_pos h, if_pos h, ins_snd_fst_eq_tailPt_snd_fst_of_ne_zero y z hj]
    all_goals rfl
  · rw [if_neg h, if_neg h]
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
