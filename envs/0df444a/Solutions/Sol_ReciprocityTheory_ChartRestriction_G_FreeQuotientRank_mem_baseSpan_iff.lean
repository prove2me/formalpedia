-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.mem_baseSpan_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:42:45.98124+00:00
-- url     : https://prove2.me/submissions/4d2b15d8-72d4-4dc5-8659-218e2b9bd8d6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDetectStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDimensionalBaseSpan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_incU_apply_eq_lTensor
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
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    (x : F ⊗[K] V) : x ∈ baseSpan F U ↔ LinearMap.lTensor F U.mkQ x = 0 := by
  have hex := lTensor_exact F (LinearMap.exact_subtype_mkQ U) (Submodule.mkQ_surjective U)
  rw [hex x, baseSpan_eq_range, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y, (incU_apply_eq_lTensor F U y).symm⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, incU_apply_eq_lTensor F U y⟩
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
