-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank.span_tmul_one
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T04:45:36.561509+00:00
-- url     : https://prove2.me/submissions/59cd0398-201e-4169-a649-38ae0f699ae7

import Mathlib
open NumberField Module
open scoped TensorProduct
variable {K K₁ V : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V]


theorem solution : Submodule.span K₁ (Set.range fun v : V => (1 : K₁) ⊗ₜ[K] v) = ⊤ := by
  apply top_unique; intro x hx; clear hx; induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a v =>
    have hv := Submodule.subset_span (R := K₁) (Set.mem_range_self (f := fun v : V => (1 : K₁) ⊗ₜ[K] v) v)
    simpa [TensorProduct.smul_tmul',smul_eq_mul] using (Submodule.smul_mem _ a hv)
  | add a b ha hb => exact Submodule.add_mem _ ha hb
