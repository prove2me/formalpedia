-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis.inner_iota
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:59:36.569803+00:00
-- url     : https://prove2.me/submissions/1bd99237-b966-411d-8d39-3f15df6ac6ae

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
theorem _root_.solution (x y : E) :
    inner ℝ (iota E x) (iota E y) = ∑ w : CP E, (w.1.embedding x * conj (w.1.embedding y)).re := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [iota_apply, iota_apply, Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis
