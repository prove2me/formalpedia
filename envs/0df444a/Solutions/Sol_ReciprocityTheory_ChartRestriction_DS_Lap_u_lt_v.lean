-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.u_lt_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:26:18.766388+00:00
-- url     : https://prove2.me/submissions/482de2d6-bc32-4330-85ae-9c5db2d5f09e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_InterlacesULt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_u_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem _root_.solution {k r : ℕ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ}
    (hI : Interlaces k r u v b) (i : ℕ) (hi : i < k - 1) (j : Fin k) (hij : i < j.val) :
    u j < v ⟨i, hi⟩ := by
  have h := (hI.1 ⟨i, hi⟩).2
  rcases Nat.lt_or_ge (i + 1) j.val with h1 | h1
  · exact lt_trans (u_lt hI ⟨i + 1, by omega⟩ j h1) h
  · have hj : j = ⟨i + 1, by omega⟩ := Fin.ext (show j.val = i + 1 by omega)
    rw [hj]
    exact h
end ReciprocityTheory.ChartRestriction.DS.Lap
