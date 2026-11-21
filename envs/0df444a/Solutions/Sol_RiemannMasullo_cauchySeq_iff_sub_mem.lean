-- Prove2me | solution 1 for RiemannMasullo.cauchySeq_iff_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:20:55.551599+00:00
-- url     : https://prove2.me/submissions/0cd7d64f-d713-461e-81df-d7475c39aaf1

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L77-L81
import Mathlib

open Set Filter Topology TopologicalSpace Bornology

universe u
variable {E : Type u} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
variable {J : Type*} [Preorder J] [Nonempty J] [IsDirectedOrder J]

theorem solution (f : J → E) :
    CauchySeq f ↔ ∀ U ∈ 𝓝 (0 : E), ∃ j₀, ∀ j ≥ j₀, ∀ k ≥ j₀, f j - f k ∈ U := by
  rw [CauchySeq, IsUniformAddGroup.cauchy_map_iff_tendsto, and_iff_right atTop_neBot,
    prod_atTop_atTop_eq, tendsto_iff_forall_eventually_mem]
  simp only [eventually_atTop_prod_self']
