-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_bound__p2m_2e520467_0d96_4c71_b340_b60069871ecd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:22:08.279444+00:00
-- url     : https://prove2.me/submissions/53f666f9-cf65-4f55-88c9-6bccf07ed805
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_82dc859a_8068_4b67_a69e_69714826e35e_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hconn : H.Connected)
    (hV : 3 <= Fintype.card V) : H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨K, hsub, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_82dc859a_8068_4b67_a69e_69714826e35e_a1
      H hH hconn hV
  have hle : H.edgeSet.ncard <= K.edgeSet.ncard := Set.ncard_mono hsub
  omega