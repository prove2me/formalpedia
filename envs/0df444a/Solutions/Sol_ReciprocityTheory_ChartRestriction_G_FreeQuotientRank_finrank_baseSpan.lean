-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finrank_baseSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:05:46.127017+00:00
-- url     : https://prove2.me/submissions/a5a00c7d-c2fd-4a67-a17b-b44f544be7d8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDetectStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDimensionalBaseSpan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_baseSpan_eq_range
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_incU_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
open TensorProduct
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {Ω : Type*} [Field Ω] [Algebra K Ω]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    [FiniteDimensional K U] : Module.finrank F (baseSpan F U) = Module.finrank K U := by
  rw [baseSpan_eq_range, LinearMap.finrank_range_of_inj (incU_injective F U),
    Module.finrank_baseChange]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
