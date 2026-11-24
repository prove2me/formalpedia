-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank.tmul_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T04:45:26.79359+00:00
-- url     : https://prove2.me/submissions/50d0b4a7-3dac-4543-b10a-0b808bf225cb

import Mathlib
open NumberField Module
open scoped TensorProduct
variable {K K₁ V : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V]


theorem solution {ι : Type*} (g : ι → V) {y : V} (hy : y ∈ Submodule.span K (Set.range g)) :
    (1 : K₁) ⊗ₜ[K] y ∈ Submodule.span K₁ (Set.range fun j => (1 : K₁) ⊗ₜ[K] g j) := by
  induction hy using Submodule.span_induction with
  | mem z hz => obtain ⟨j,rfl⟩ := hz; exact Submodule.subset_span ⟨j,rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    have H := Submodule.smul_mem (Submodule.span K₁ (Set.range fun j => (1:K₁) ⊗ₜ[K] g j)) (algebraMap K K₁ c) ha
    simpa [← TensorProduct.smul_tmul,TensorProduct.smul_tmul', Algebra.smul_def] using H
