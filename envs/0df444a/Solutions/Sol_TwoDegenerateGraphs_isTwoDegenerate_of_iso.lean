-- Prove2me | solution 1 for TwoDegenerateGraphs.isTwoDegenerate_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/c8ce6d5c-74a6-4d27-bc8d-8fc562d692f3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : IsTwoDegenerate G) :
    IsTwoDegenerate H := by
  classical
  intro s hs
  let t : Finset V := s.map e.symm.toEquiv.toEmbedding
  have ht : t.Nonempty := by
    obtain ⟨w, hw⟩ := hs
    refine ⟨e.symm w, ?_⟩
    exact Finset.mem_map.mpr ⟨w, hw, rfl⟩
  obtain ⟨v, hv, hcard⟩ := hG t ht
  refine ⟨e v, ?_, ?_⟩
  · change v ∈ s.map e.symm.toEquiv.toEmbedding at hv
    obtain ⟨w, hw, heq⟩ := Finset.mem_map.mp hv
    have hwv : w = e v := by
      apply e.symm.toEquiv.injective
      simpa using heq
    simpa [← hwv] using hw
  · have hneighbors :
        neighborsWithin H s (e v) =
          (neighborsWithin G t v).map e.toEquiv.toEmbedding := by
      ext w
      simp only [neighborsWithin, Finset.mem_filter, Finset.mem_map_equiv]
      have hmembership : e.symm w ∈ t ↔ w ∈ s := by
        change e.symm w ∈ s.map e.symm.toEquiv.toEmbedding ↔ w ∈ s
        constructor
        · intro hmember
          obtain ⟨u, hu, heq⟩ := Finset.mem_map.mp hmember
          have huw : u = w := e.symm.toEquiv.injective heq
          simpa [huw] using hu
        · intro hmember
          exact Finset.mem_map.mpr ⟨w, hmember, rfl⟩
      have hadjacency :
          G.Adj v (e.symm w) ↔ H.Adj (e v) w := by
        simpa using (e.map_rel_iff (a := v) (b := e.symm w)).symm
      exact (and_congr hmembership hadjacency).symm
    rw [hneighbors, Finset.card_map]
    exact hcard
end TwoDegenerateGraphs
