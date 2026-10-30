-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_e54811a8_cc12_4b66_a567_2bf19301ebf6_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:24:23.002143+00:00
-- url     : https://prove2.me/submissions/40aaea2d-245c-4a44-a3b8-36dfb9495840
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_826e5589_6c55_45ce_83c1_aa1fee8116e2_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_826e5589_6c55_45ce_83c1_aa1fee8116e2_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hEdges, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_826e5589_6c55_45ce_83c1_aa1fee8116e2_a2
      G hG
  have hbound :=
    WilliamsonShmoys.maximal_planar_edge_bound__p2m_826e5589_6c55_45ce_83c1_aa1fee8116e2_a2
      H hH hV hmax
  have hcard : G.edgeSet.ncard ≤ H.edgeSet.ncard :=
    Set.ncard_mono hEdges
  omega
