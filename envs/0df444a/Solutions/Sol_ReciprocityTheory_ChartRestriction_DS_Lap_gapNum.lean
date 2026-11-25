-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.gapNum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:26:03.224918+00:00
-- url     : https://prove2.me/submissions/926240fc-bcfb-426a-bbb8-9bde4352e10d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_SpectralGap_GapNum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_gapNum_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem _root_.solution : GapNumStatement := by
  intro n q t x hn hq hqn ht hx
  unfold hNum
  have hx' : 2 * ((n : ℝ) + 2 * (q : ℝ) * (t : ℝ)) ^ 3 + (t : ℝ) + 3 < x := by
    push_cast at hx; exact hx
  exact gapNum_real (q : ℝ) (n : ℝ) (t : ℝ) ((n - q : ℕ) : ℝ) ((min (n - q) q : ℕ) : ℝ) x
    (by exact_mod_cast hq) (by exact_mod_cast hn) (by exact_mod_cast ht)
    (by exact_mod_cast Nat.sub_le n q) (Nat.cast_nonneg _)
    (by exact_mod_cast min_le_right _ _) hx'
end ReciprocityTheory.ChartRestriction.DS.Lap
