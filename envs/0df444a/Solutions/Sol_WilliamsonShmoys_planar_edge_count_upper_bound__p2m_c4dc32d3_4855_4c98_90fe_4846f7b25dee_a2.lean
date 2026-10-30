-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c4dc32d3_4855_4c98_90fe_4846f7b25dee_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:29:05.770126+00:00
-- url     : https://prove2.me/submissions/0ea59a6b-f51b-4ee1-a1fa-ebba6a8049e7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper_bound__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨N, hMN, hNconn, hNplanar⟩ :=
    WilliamsonShmoys.exists_connected_planar_supergraph__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1
      M hM hCard
  have hEdges : M.edgeSet ⊆ N.edgeSet := SimpleGraph.edgeSet_mono hMN
  have hNbound :=
    WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1
      N hNconn hNplanar hCard
  have hMono : M.edgeSet.ncard <= N.edgeSet.ncard := Set.ncard_mono hEdges
  omega