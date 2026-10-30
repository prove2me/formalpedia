-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph_extension__p2m_219a8e3b_c7d8_43b3_9ee1_a4b3ebf8e3f2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:36:11.411654+00:00
-- url     : https://prove2.me/submissions/d30af4d6-e26d-45a5-84c3-7a03c361ae97

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by
  classical
  let s : Set (SimpleGraph V) := {G | K ≤ G ∧ HasPlanarDrawingOn G}
  have hs : s.Finite := Set.toFinite s
  have hne : s.Nonempty := ⟨K, le_rfl, hK⟩
  obtain ⟨L, hL, hmax⟩ := hs.exists_maximal hne
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro M hLM hM
  have hMs : M ∈ s := ⟨hL.1.trans hLM, hM⟩
  have hML : M ≤ L := hmax hMs hLM
  exact le_antisymm hML hLM