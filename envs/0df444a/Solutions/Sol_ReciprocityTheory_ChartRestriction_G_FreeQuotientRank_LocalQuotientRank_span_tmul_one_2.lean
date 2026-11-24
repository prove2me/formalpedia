-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank.span_tmul_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:51.270363+00:00
-- url     : https://prove2.me/submissions/3149b42b-05e6-4297-90b0-cdb8fb74ba13

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
theorem _root_.solution : Submodule.span K₁ (Set.range fun v : V => (1 : K₁) ⊗ₜ[K] v) = ⊤ := by
  rw [eq_top_iff]
  rintro t -
  induction t using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a v =>
    have : a ⊗ₜ[K] v = a • ((1 : K₁) ⊗ₜ[K] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank
