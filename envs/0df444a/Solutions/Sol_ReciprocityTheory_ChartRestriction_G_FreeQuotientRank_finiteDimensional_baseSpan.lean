-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finiteDimensional_baseSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:34:09.36054+00:00
-- url     : https://prove2.me/submissions/dfe145fd-23b5-414a-b1fb-1d1fe5c6830a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDetectStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDimensionalBaseSpan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_baseSpan_eq_range

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
    [FiniteDimensional K U] : FiniteDimensional F (baseSpan F U) := by
  rw [baseSpan_eq_range]; infer_instance
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
