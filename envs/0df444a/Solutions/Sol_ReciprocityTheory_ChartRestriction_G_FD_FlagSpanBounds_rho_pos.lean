-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds.rho_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:47.574094+00:00
-- url     : https://prove2.me/submissions/e366c7aa-54f0-466c-9d4b-87ffe1301dde

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NonvanishingNearMaximumHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlagSpanBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds
theorem _root_.solution {w : ℝ} (hw1 : 1 ≤ w) (hr : 0 < r) : 0 < frameRadius w r ∧ frameRadius w r ≤ 1 / 10 := by
  unfold frameRadius
  have hwr : 1 ≤ w * (r : ℝ) := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  have hs : 1 ≤ √(w * r) := by
    first
    | exact Real.one_le_sqrt.mpr hwr
    | exact (Real.sqrt_one).symm ▸ Real.sqrt_le_sqrt hwr
  constructor
  · apply div_pos one_pos
    linarith
  · exact one_div_le_one_div_of_le (by norm_num) (by linarith)
end ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds
