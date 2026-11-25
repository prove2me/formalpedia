-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds.trace_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:56:39.401722+00:00
-- url     : https://prove2.me/submissions/8e384713-f1da-4eb2-b9e6-0f34c13cfe15

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralTraceNormBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralTraceNormBounds_trace_ed

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
theorem _root_.solution (c : Free.ChooseBasisIndex ℤ (𝓞 E) → ℤ) (γ : 𝓞 E) :
    ∃ m : ℤ, Algebra.trace ℚ E ((∑ j, c j • ed E j) * (γ : E)) = m := by
  obtain ⟨m, hm⟩ : ∃ m : Free.ChooseBasisIndex ℤ (𝓞 E) → ℤ,
      (γ : E) = ∑ i, m i • integralBasis E i := by
    refine ⟨(RingOfIntegers.basis E).repr γ, ?_⟩
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr γ]
    simp [integralBasis_apply]
  have key : ∀ j i, Algebra.trace ℚ E ((c j • ed E j) * (m i • integralBasis E i)) =
      if i = j then ((c j * m i : ℤ) : ℚ) else 0 := by
    intro j i
    rw [smul_mul_smul_comm, map_zsmul, mul_comm (ed E j), trace_ed]
    split_ifs <;> simp
  refine ⟨∑ j, c j * m j, ?_⟩
  rw [hm, Finset.sum_mul_sum, map_sum]
  simp_rw [map_sum, key]
  simp [Finset.sum_ite_eq']
end ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds
