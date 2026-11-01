-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_3b0cc7ba_e438_41c2_b251_7b0cfc52f510_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:43:56.947738+00:00
-- url     : https://prove2.me/submissions/6288e0b8-5059-41b8-a3c6-c9eeb7ec2ec9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_a9c9dbb0_74a5_4e80_aeeb_6c6cfc8d46c4_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound__p2m_a9c9dbb0_74a5_4e80_aeeb_6c6cfc8d46c4_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      L.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  obtain ⟨H, hLH, hHdraw, hHmax, hcards⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a9c9dbb0_74a5_4e80_aeeb_6c6cfc8d46c4_a2 L hL
  have hbound :=
    WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_a9c9dbb0_74a5_4e80_aeeb_6c6cfc8d46c4_a2 H hHdraw hcard hHmax
  exact le_trans (Nat.add_le_add_right hcards 6) hbound