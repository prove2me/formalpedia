-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.adjGap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:24:37.110559+00:00
-- url     : https://prove2.me/submissions/3e402b71-498f-42ce-ab4d-e074ca9f0bc0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_adjGap_lt

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
theorem _root_.solution : AdjGapStatement := by
  unfold AdjGapStatement GapAtLeast
  intro n ε lam h hs hadj a b hab
  rcases lt_trichotomy a.val b.val with hlt | heq | hgt
  · exact le_trans (adjGap_lt ε lam h hs hadj a b hlt hab) (le_abs_self _)
  · exact absurd (congrArg ε (Fin.ext heq)) hab
  · rw [abs_sub_comm]
    exact le_trans (adjGap_lt ε lam h hs hadj b a hgt hab.symm) (le_abs_self _)
end ReciprocityTheory.ChartRestriction.DS.Lap
