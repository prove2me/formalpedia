-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion.mul_sign_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:59:52.674625+00:00
-- url     : https://prove2.me/submissions/b266fca0-ce29-40ea-b0a0-591b68396641

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
theorem _root_.solution (a : ℤ) : (a : ℝ) * (a.sign : ℝ) = |(a : ℝ)| := by
  rcases lt_trichotomy a 0 with h | rfl | h
  · rw [Int.sign_eq_neg_one_of_neg h, abs_of_neg (by exact_mod_cast h)]
    push_cast
    ring
  · simp
  · rw [Int.sign_eq_one_of_pos h, abs_of_pos (by exact_mod_cast h)]
    push_cast
    ring
end ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
