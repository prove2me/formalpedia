-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis.bas_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:21.162857+00:00
-- url     : https://prove2.me/submissions/37070567-a0be-430f-86a6-cda968f16fcd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis

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
theorem _root_.solution (i : Free.ChooseBasisIndex ℤ (𝓞 E)) : bas E i = iota E (integralBasis E i) := by
  rw [bas, Basis.map_apply, mixedEmbedding.latticeBasis_apply]
  first
    | rfl
    | (ext w; simp [toVS, iota, mixedEmbedding])
end ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis
