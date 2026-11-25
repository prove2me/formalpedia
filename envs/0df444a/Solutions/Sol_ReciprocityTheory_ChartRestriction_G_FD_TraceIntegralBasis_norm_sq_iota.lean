-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis.norm_sq_iota
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:59:43.045269+00:00
-- url     : https://prove2.me/submissions/bc64492f-e33f-455e-ae07-2925f915739c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_iota_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis
open NumberField InfinitePlace Module Submodule
open scoped ComplexConjugate Classical
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}
namespace ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis
theorem _root_.solution (x : E) : ‖iota E x‖ ^ 2 = ∑ w : CP E, ‖w.1.embedding x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [iota_apply]
end ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis
