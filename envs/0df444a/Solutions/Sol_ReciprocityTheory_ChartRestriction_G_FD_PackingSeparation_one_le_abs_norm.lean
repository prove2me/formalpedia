-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation.one_le_abs_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:57.672065+00:00
-- url     : https://prove2.me/submissions/26913729-885e-4fb8-a7b4-ad61f9971792

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralTraceNormBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PackingSeparation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation
open NumberField InfinitePlace Module MeasureTheory Metric TraceIntegralBasis IntegralTraceNormBounds
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation
theorem _root_.solution (γ : 𝓞 E) (hγ : γ ≠ 0) : 1 ≤ |(Algebra.norm ℚ (γ : E) : ℝ)| := by
  have h := Algebra.coe_norm_int γ
  have hne : Algebra.norm ℤ γ ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at h
    exact (Algebra.norm_ne_zero_iff.mpr (by exact_mod_cast hγ : (γ : E) ≠ 0)) h.symm
  rw [← h]
  have := Int.one_le_abs hne
  push_cast
  exact_mod_cast this
end ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation
