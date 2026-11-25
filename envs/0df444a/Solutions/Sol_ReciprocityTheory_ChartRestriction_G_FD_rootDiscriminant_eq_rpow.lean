-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.rootDiscriminant_eq_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:01:30.859749+00:00
-- url     : https://prove2.me/submissions/92069449-7562-49de-b2b8-34463ec0c9ad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankEqTwoMulHalfDegree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_finrank_eq_two_mul_half_degree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution : rdE E = dE E ^ (1 / (2 * (fdeg E : ℝ))) := by
  unfold rdE
  rw [finrank_eq_two_mul_half_degree]
end ReciprocityTheory.ChartRestriction.G.FD
