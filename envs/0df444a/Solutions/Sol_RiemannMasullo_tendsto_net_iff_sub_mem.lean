-- Prove2me | solution 1 for RiemannMasullo.tendsto_net_iff_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:20:54.916444+00:00
-- url     : https://prove2.me/submissions/08234d6d-7d8d-4961-8ce6-5dcd69916eaf

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L70-L73
import Mathlib

open Set Filter Topology TopologicalSpace Bornology

universe u
variable {E : Type u} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
variable {J : Type*} [Preorder J] [Nonempty J] [IsDirectedOrder J]

theorem solution (f : J → E) (x : E) :
    Tendsto f atTop (𝓝 x) ↔ ∀ U ∈ 𝓝 (0 : E), ∃ j₀, ∀ j ≥ j₀, x - f j ∈ U := by
  rw [← tendsto_const_sub_iff x, sub_self, tendsto_iff_forall_eventually_mem]
  simp only [eventually_atTop]
