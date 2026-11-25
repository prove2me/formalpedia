-- Prove2me | solution 1 for PI.HtPlacesSumWork.valPl_log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:59.099802+00:00
-- url     : https://prove2.me/submissions/99eb3192-5a39-4829-9c4b-f5453a275f83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_ValPlWtAddEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.HtPlacesSumWork
open IsDedekindDomain WithZero IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
namespace PI.HtPlacesSumWork
theorem _root_.solution {g : ℤᵐ⁰} (hg : g ≠ 0) : g ≤ 1 ↔ log g ≤ 0 := by
  rw [← log_le_log hg one_ne_zero, log_one]
end PI.HtPlacesSumWork
