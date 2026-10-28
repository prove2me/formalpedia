-- Prove2me | solution 1 for Submodule.starProjection_map_eq_zero_iff_forall_dotProduct
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T05:15:22.431355+00:00
-- url     : https://prove2.me/submissions/44d90aca-f9a7-40e9-af9b-678b568faf3b

import Mathlib

-- carved verbatim out of submission 3c55ced4-4944-4de2-ba43-8110d2682db1, lines 2628-2648

section
open Matrix

theorem solution {N : ℕ} (V : Submodule ℝ (Fin N → ℝ))
    (b : Fin N → ℝ) :
    (V.map (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm.toLinearMap).starProjection
        (WithLp.toLp 2 b) = 0 ↔ ∀ v ∈ V, b ⬝ᵥ v = 0 := by
  rw [Submodule.starProjection_apply, Submodule.coe_eq_zero,
    Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.mem_orthogonal]
  constructor
  · intro h v hv
    have := h _ (Submodule.mem_map_of_mem hv)
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    simpa using this
  · intro h u hu
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hu
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simpa using h v hv

end
