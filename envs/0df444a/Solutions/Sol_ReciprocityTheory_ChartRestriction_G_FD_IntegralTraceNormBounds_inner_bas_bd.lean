-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds.inner_bas_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:14:54.363741+00:00
-- url     : https://prove2.me/submissions/4a9cbc97-c3fd-498e-bc1e-42f561f90c9d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralTraceNormBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralTraceNormBounds_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralTraceNormBounds_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralTraceNormBounds_cc_two
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralTraceNormBounds_inner_iota_eq_trace
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralTraceNormBounds_trace_ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_bas_apply


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
theorem _root_.solution (i j : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    inner ℝ (bas E i) (bd E j) = if i = j then 1 else 0 := by
  rw [bas_apply, bd, inner_iota_eq_trace, cc_mul, cc_cc, cc_two]
  have h2 : integralBasis E i * (2 * ed E j) = (2 : ℚ) • (integralBasis E i * ed E j) := by
    rw [Algebra.smul_def, map_ofNat]
    ring
  rw [h2, LinearMap.map_smul, trace_ed]
  split_ifs <;> norm_num
end ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds
