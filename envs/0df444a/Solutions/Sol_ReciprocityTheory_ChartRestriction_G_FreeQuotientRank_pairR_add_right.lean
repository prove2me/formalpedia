-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.pairR_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:00:59.98649+00:00
-- url     : https://prove2.me/submissions/a437862f-e722-4877-8bc6-94b8608eca4c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BetaSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BetaPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Finset
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution {f : ℕ} (u v w : Fin f → ℝ) : pairR u (v + w) = pairR u v + pairR u w := by
  unfold pairR
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
