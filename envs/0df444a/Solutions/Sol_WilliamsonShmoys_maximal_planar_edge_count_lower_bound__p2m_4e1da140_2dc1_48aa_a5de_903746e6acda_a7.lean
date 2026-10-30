-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_4e1da140_2dc1_48aa_a5de_903746e6acda_a7
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T04:55:13.91592+00:00
-- url     : https://prove2.me/submissions/370386f0-e506-48f6-8b1b-42e9bb5756f6

import Mathlib.Tactic
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_bound__p2m_accf786d_4436_4249_b439_8ab55fe05a76_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hLmax : forall M : SimpleGraph V,
      L.edgeSet <= M.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      M.edgeSet <= L.edgeSet) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hMplanar, hMbound⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_edge_bound__p2m_accf786d_4436_4249_b439_8ab55fe05a76_a3
      L hV hLplanar
  have hML : M.edgeSet <= L.edgeSet := hLmax M hLM hMplanar
  have hcard : M.edgeSet.ncard <= L.edgeSet.ncard := Set.ncard_le_ncard hML
  omega