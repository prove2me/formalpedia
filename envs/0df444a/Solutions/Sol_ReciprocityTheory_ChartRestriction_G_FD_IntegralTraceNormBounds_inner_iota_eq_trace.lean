-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds.inner_iota_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:06:44.730556+00:00
-- url     : https://prove2.me/submissions/3aa38a3f-8cda-48a0-8f59-17a860b3039d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralTraceNormBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_inner_iota
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_sum_re_eq_trace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds
open NumberField InfinitePlace Module Submodule TraceIntegralBasis
open scoped ComplexConjugate Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds
theorem _root_.solution (x y : E) :
    inner ℝ (iota E x) (iota E y) = (1 / 2 : ℝ) * (Algebra.trace ℚ E (x * cc y) : ℝ) := by
  rw [inner_iota, ← sum_re_eq_trace]
  apply Finset.sum_congr rfl
  intro w _
  simp only [cc, map_mul, IsCMField.complexEmbedding_complexConj]
end ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds
