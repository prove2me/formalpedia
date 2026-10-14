-- Prove2me | solution 1 for StabilityConjecture.omegaStable_of_structurallyStable
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-11T20:09:57.27882+00:00
-- url     : https://prove2.me/submissions/cdeb1bda-66b0-4570-ab33-25281d91ab53

import Mathlib
import Definitions.Def_ClosingLemma_DiffeoCrTopology
import Definitions.Def_PughClosingLemma_nonwandering
import Definitions.Def_StabilityConjecture_Basic

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open StabilityConjecture ClosingLemma

namespace SC_A

theorem nonwandering_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → X) (G : Y → Y) (h : X ≃ₜ Y) (hconj : ∀ x, h (F x) = G (h x)) (x : X)
    (hx : x ∈ PughClosingLemma.nonwanderingSet F) :
    h x ∈ PughClosingLemma.nonwanderingSet G := by
  intro V hV
  have hU : (⇑h) ⁻¹' V ∈ 𝓝 x := h.continuous.continuousAt.preimage_mem_nhds hV
  obtain ⟨k, hk, z, ⟨w, hw, rfl⟩, hz⟩ := hx _ hU
  have hsc : Function.Semiconj h F G := hconj
  refine ⟨k, hk, h (F^[k] w), ⟨h w, hw, ?_⟩, hz⟩
  exact (hsc.iterate_right k w).symm

theorem nonwandering_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → X) (G : Y → Y) (h : X ≃ₜ Y) (hconj : ∀ x, h (F x) = G (h x)) :
    PughClosingLemma.nonwanderingSet F = (⇑h) ⁻¹' PughClosingLemma.nonwanderingSet G := by
  ext x
  refine ⟨nonwandering_map F G h hconj x, fun hx => ?_⟩
  have hconj' : ∀ y, h.symm (G y) = F (h.symm y) := by
    intro y
    apply h.injective
    rw [hconj, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  have := nonwandering_map G F h.symm hconj' (h x) hx
  simpa using this

end SC_A

theorem solution {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (r : ℕ) (f : Diff n M r) (hf : IsStructurallyStable r f) :
    IsOmegaStable r f := by
  obtain ⟨U, hU, hUconj⟩ := hf
  refine ⟨U, hU, fun g hg => ?_⟩
  obtain ⟨h, hh⟩ := hUconj g hg
  refine ⟨h.sets (SC_A.nonwandering_iff (⇑f) (⇑g) h hh), fun x y hxy => ?_⟩
  show h (y : M) = g (h (x : M))
  rw [hxy, hh]
