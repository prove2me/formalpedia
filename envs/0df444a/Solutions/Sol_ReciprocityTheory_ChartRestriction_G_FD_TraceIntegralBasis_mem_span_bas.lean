-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis.mem_span_bas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:59:40.329113+00:00
-- url     : https://prove2.me/submissions/3acc5542-03c5-4889-8ad4-ba8cd94c5f00

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_bas_apply

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
variable (E)
variable {E}
namespace ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis
theorem _root_.solution {x : VS E} (hx : x ∈ span ℤ (Set.range (bas E))) :
    ∃ α : 𝓞 E, x = iota E (α : E) := by
  obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
  refine ⟨∑ i, c i • RingOfIntegers.basis E i, ?_⟩
  simp only [bas_apply, integralBasis_apply, ← map_zsmul, ← map_sum]
end ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis
