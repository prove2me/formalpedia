-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.inclT_mem_baseSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:52:35.460797+00:00
-- url     : https://prove2.me/submissions/83a99661-7e69-42af-861c-cb6c3dca5b63

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDetectStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDimensionalBaseSpan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_mem_baseSpan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_lTensor_mkQ_inclT

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
theorem _root_.solution (K₁ : IntermediateField K Ω) (U : Submodule K V) (x : K₁ ⊗[K] V)
    (h : x ∈ baseSpan K₁ U) : inclT K₁ V x ∈ baseSpan Ω U := by
  rw [mem_baseSpan_iff] at h ⊢
  rw [lTensor_mkQ_inclT, h, map_zero]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
