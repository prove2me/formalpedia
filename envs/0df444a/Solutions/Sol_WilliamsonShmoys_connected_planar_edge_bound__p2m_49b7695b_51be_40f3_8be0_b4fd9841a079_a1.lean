-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_49b7695b_51be_40f3_8be0_b4fd9841a079_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:28:45.560416+00:00
-- url     : https://prove2.me/submissions/9e346691-cfe2-4394-b181-b63a84fea000
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_ed9a163f_a427_4bb6_adf9_73a7e049aa03_a1
import Theorems.Thm_WilliamsonShmoys_finite_edgeSet_ncard_mono__p2m_ed9a163f_a427_4bb6_adf9_73a7e049aa03_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hplanar : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, _hHplanar, hHedges⟩ :=
    WilliamsonShmoys_planar_triangulation_extension__p2m_ed9a163f_a427_4bb6_adf9_73a7e049aa03_a1
      G hconn hplanar hV
  have hmono :=
    WilliamsonShmoys_finite_edgeSet_ncard_mono__p2m_ed9a163f_a427_4bb6_adf9_73a7e049aa03_a1
      G H hGH
  omega