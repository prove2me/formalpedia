-- Prove2me | solution 1 for PughClosingLemma.image_nonwanderingSet
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:12:13.287546+00:00
-- url     : https://prove2.me/submissions/40a71038-25fd-49c1-9556-4ed86c039194

import Definitions.Def_PughClosingLemma_nonwandering

open scoped Topology
open PughClosingLemma

namespace ContTopology

lemma transport_nonwandering {X : Type*} [TopologicalSpace X] (f : X → X)
    (g : X ≃ₜ X) (h : Function.Commute f g) {x : X} (hx : IsNonwandering f x) :
    IsNonwandering f (g x) := by
  intro U hU
  obtain ⟨n, hn, z, ⟨y, hy, rfl⟩, hz⟩ :=
    hx (g ⁻¹' U) (g.continuous.continuousAt.preimage_mem_nhds hU)
  refine ⟨n, hn, g (f^[n] y), ⟨g y, hy, ?_⟩, hz⟩
  exact h.iterate_left n y

end ContTopology

theorem solution {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) :
    f '' nonwanderingSet f = nonwanderingSet f := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact ContTopology.transport_nonwandering f f (Function.Commute.refl f) hx
  · intro x hx
    refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
    exact ContTopology.transport_nonwandering f f.symm (by intro y; simp) hx
