-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_9518e4d8_9181_45e5_8d65_e8b1bfbc442a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:03:03.26721+00:00
-- url     : https://prove2.me/submissions/728629ca-ff01-4c49-bc89-73e7b15b9063

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_61543ccf_c10c_45ac_85dc_db241ebaf64e_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : forall K : SimpleGraph V, G <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K = G) :
    3 * Fintype.card V - 6 <= G.edgeSet.ncard := by
  obtain ⟨K, hGK, hKplanar, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_61543ccf_c10c_45ac_85dc_db241ebaf64e_a1
      G hcard hG
  have hKG : K = G := hmax K hGK hKplanar
  rw [← hKG]
  omega