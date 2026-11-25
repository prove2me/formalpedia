-- Prove2me | solution 1 for PI.HtPlacesSumWork.valPl_log_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:43:03.136439+00:00
-- url     : https://prove2.me/submissions/3f1c3467-d0f2-4a09-bc62-784c7cb97346

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
theorem _root_.solution {g : ℤᵐ⁰} (hg : g ≠ 0) : g < 1 ↔ log g < 0 := by
  rw [← not_le, ← not_le, ← log_le_log one_ne_zero hg, log_one]
end PI.HtPlacesSumWork
