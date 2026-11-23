-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.Lsq_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:27.866075+00:00
-- url     : https://prove2.me/submissions/ca0d30f8-023e-473f-b24e-79161bab73d9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc

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
theorem _root_.solution {p m : ℕ} (x : Xp p m) {l l' : Fin (p + 1)} (h : l ≤ l') : Lsq x l ≤ Lsq x l' := by
  have h' : l.val ≤ l'.val := Fin.le_iff_val_le_val.mp h
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.Lsq
  have : ∑ j : Fin p, (if j.val < l.val then ‖x.1 j‖ ^ 2 else 0) ≤
      ∑ j : Fin p, (if j.val < l'.val then ‖x.1 j‖ ^ 2 else 0) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases h1 : j.val < l.val
    · have h2 : j.val < l'.val := lt_of_lt_of_le h1 h'
      rw [if_pos h1, if_pos h2]
    · rw [if_neg h1]
      split_ifs <;> positivity
  linarith
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
