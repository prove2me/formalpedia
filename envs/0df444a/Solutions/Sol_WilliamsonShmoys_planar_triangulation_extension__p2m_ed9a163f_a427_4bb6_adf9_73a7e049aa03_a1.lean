-- Prove2me | solution 1 for WilliamsonShmoys_planar_triangulation_extension__p2m_ed9a163f_a427_4bb6_adf9_73a7e049aa03_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:32:52.264924+00:00
-- url     : https://prove2.me/submissions/6a64a0d2-6470-468e-aa23-4a7442182d19
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_2d00307b_e04d_4990_9e5d_cdabacc381df_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_2d00307b_e04d_4990_9e5d_cdabacc381df_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHplanar, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_2d00307b_e04d_4990_9e5d_cdabacc381df_a1
      G hplanar
  refine ⟨H, hGH, hHplanar, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_2d00307b_e04d_4990_9e5d_cdabacc381df_a1
    H hHplanar hV hmax