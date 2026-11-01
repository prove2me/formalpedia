-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_ff0df929_a528_472b_801c_6c58169000bb_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:20:32.500916+00:00
-- url     : https://prove2.me/submissions/dcf76133-3d22-4e00-b64d-855e42015ae1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension_exists__p2m_2a77e1c0_132e_4864_a8ba_ceda5e75c647_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_2a77e1c0_132e_4864_a8ba_ceda5e75c647_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 <= Fintype.card V) :
    Exists fun H : SimpleGraph V =>
      G <= H /\
      HasPlanarDrawingOn H /\
      G.edgeSet.ncard <= H.edgeSet.ncard /\
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHplanar, hEdges, hHconn, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_extension_exists__p2m_2a77e1c0_132e_4864_a8ba_ceda5e75c647_a2
      G hplanar hconn
  exact ⟨H, hGH, hHplanar, hEdges,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_2a77e1c0_132e_4864_a8ba_ceda5e75c647_a2
      H hHplanar hHconn hcard hmax⟩