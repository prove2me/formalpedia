-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion.abs_sign_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:00:18.700125+00:00
-- url     : https://prove2.me/submissions/aa55ea58-ed98-4de1-9691-8dabcebdc121

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeSummability
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeFourierExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
open Complex MeasureTheory Metric ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
theorem _root_.solution (a : ℤ) : |(a.sign : ℝ)| ≤ 1 := by
  rcases Int.sign_trichotomy a with h | h | h <;> simp [h]
end ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
