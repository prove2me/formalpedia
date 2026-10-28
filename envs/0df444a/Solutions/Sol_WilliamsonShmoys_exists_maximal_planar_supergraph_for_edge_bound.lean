-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:55:12.437116+00:00
-- url     : https://prove2.me/submissions/34f10c39-630a-4541-bda9-0ca6d5d2bba0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun L : SimpleGraph V => K <= L /\ WilliamsonShmoys.HasPlanarDrawingOn L /\
      (forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) := by
  classical
  let S : Set (SimpleGraph V) :=
    {L | K <= L /\ WilliamsonShmoys.HasPlanarDrawingOn L}
  have hS : S.Finite := Set.toFinite S
  obtain ⟨L, hL, hmax⟩ := hS.exists_maximal ⟨K, le_rfl, hK⟩
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro M hLM hM
  have hM' : M ∈ S := ⟨hL.1.trans hLM, hM⟩
  have hML : M ≤ L := hmax hM' hLM
  exact (le_antisymm hLM hML).symm