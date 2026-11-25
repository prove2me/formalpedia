-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.baseSpan_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:25:16.595412+00:00
-- url     : https://prove2.me/submissions/9eed5233-c1ac-4922-9e33-9da9442405db

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDetectStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDimensionalBaseSpan

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
theorem _root_.solution (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    baseSpan F U = LinearMap.range (incU F U) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨(1 : F) ⊗ₜ[K] (⟨u, hu⟩ : U), by simp [incU]⟩
  · rintro _ ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a u =>
      have : incU F U (a ⊗ₜ[K] u) = a • ((1 : F) ⊗ₜ[K] (u : V)) := by
        simp [incU, TensorProduct.smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, u.2, rfl⟩)
    | add y z hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
