-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.pairR_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:01:05.813182+00:00
-- url     : https://prove2.me/submissions/7c3c3dbe-72ab-4a16-88d5-f61687daee75

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
theorem _root_.solution {f : ℕ} (u v w : Fin f → ℝ) : pairR (u - v) w = pairR u w - pairR v w := by
  simp only [pairR, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
