-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank.tmul_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:51.443808+00:00
-- url     : https://prove2.me/submissions/014231ad-6d96-4e38-bbc2-b0477b05a72a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FreeQuotPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalQuotientRank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank
open NumberField Module
open scoped TensorProduct
variable {K K₁ V : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank
theorem _root_.solution {ι : Type*} (g : ι → V) {y : V} (hy : y ∈ Submodule.span K (Set.range g)) :
    (1 : K₁) ⊗ₜ[K] y ∈ Submodule.span K₁ (Set.range fun j => (1 : K₁) ⊗ₜ[K] g j) := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨j, rfl⟩ := hy; exact Submodule.subset_span ⟨j, rfl⟩
  | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha =>
    rw [TensorProduct.tmul_smul, ← algebraMap_smul K₁ r]
    exact Submodule.smul_mem _ _ ha
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank
