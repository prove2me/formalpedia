-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.iic_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:18:24.482048+00:00
-- url     : https://prove2.me/submissions/fcd9451f-3294-49b9-ad3f-86c8d1f04c52

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_CriticalExponentSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailFinOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_sum_Iic

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
theorem _root_.solution {p : ℕ} (ν : Fin (p + 2) → ℝ) (l : Fin (p + 1)) :
    ∑ j ∈ Finset.Iic l.succ, ν j = ν 0 + ∑ j ∈ Finset.Iic l, ν j.succ := by
  rw [sum_Iic, sum_Iic (fun j => ν j.succ), Fin.sum_univ_succ (n := p + 1)]
  simp [Fin.succ_le_succ_iff]
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
