-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds.cc_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:56:34.228769+00:00
-- url     : https://prove2.me/submissions/064fc608-8a62-4e98-8edd-53cd7d7d4395

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralTraceNormBounds

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
theorem _root_.solution : cc (2 : E) = 2 := by
  unfold cc
  exact map_ofNat _ 2
end ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds
