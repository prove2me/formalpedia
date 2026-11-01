-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph__p2m_78cb0e01_1105_4561_a4db_7810010c8df8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:06:11.31818+00:00
-- url     : https://prove2.me/submissions/883b51f3-df7e-44a8-93e8-41e7afb73e19

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) :
    ∃ (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj),
      HasPlanarDrawingOn Q ∧ G ≤ Q ∧
      (∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
        HasPlanarDrawingOn K → Q ≤ K → K = Q) := by
  classical
  let s : Set (SimpleGraph V) := {K | G ≤ K ∧ HasPlanarDrawingOn K}
  have hs : s.Finite := Set.toFinite s
  have hne : s.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨Q, hQ, hmax⟩ := hs.exists_maximal hne
  refine ⟨Q, inferInstance, hQ.2, hQ.1, ?_⟩
  intro K dK hK hQK
  have hGK : G ≤ K := le_trans hQ.1 hQK
  have hKmem : K ∈ s := ⟨hGK, hK⟩
  have hKQ : K ≤ Q := hmax hKmem hQK
  exact le_antisymm hKQ hQK