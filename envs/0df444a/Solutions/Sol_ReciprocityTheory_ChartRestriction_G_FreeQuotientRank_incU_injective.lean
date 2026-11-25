-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.incU_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:01:34.867531+00:00
-- url     : https://prove2.me/submissions/8055797c-a62d-4ccf-acc5-2bb7235c2839

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDetectStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDimensionalBaseSpan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_incU_apply_eq_lTensor

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
theorem _root_.solution (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    Function.Injective (incU F U) := by
  intro x y h
  rw [incU_apply_eq_lTensor, incU_apply_eq_lTensor] at h
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := F) U.subtype U.injective_subtype h
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
