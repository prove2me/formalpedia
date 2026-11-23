-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds.prod_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:46.02916+00:00
-- url     : https://prove2.me/submissions/080d0a14-82a7-4199-8bd5-ed6770ea68d1

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
theorem _root_.solution (β : E) :
    ∏ w : CP E, ‖w.1.embedding β‖ ^ 2 = |(Algebra.norm ℚ β : ℝ)| := by
  rw [← Rat.cast_abs, ← NumberField.InfinitePlace.prod_eq_abs_norm,
    ← (Equiv.subtypeUnivEquiv (fun w : InfinitePlace E => IsTotallyComplex.isComplex w)).prod_comp]
  apply Finset.prod_congr rfl
  intro w _
  rw [InfinitePlace.norm_embedding_eq]
  change w.1 β ^ 2 = w.1 β ^ w.1.mult
  rw [InfinitePlace.mult_isComplex]
end ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds
