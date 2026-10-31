-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_4d9bb183_475b_4a59_8b75_1a8cda8dae1d_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:22:46.076988+00:00
-- url     : https://prove2.me/submissions/c36b6b9d-e22b-44a9-8d24-829de91409fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_6fab6ec6_c4a2_4215_b61d_4e14bbc8fe70_a2
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_6fab6ec6_c4a2_4215_b61d_4e14bbc8fe70_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel L.Adj := dL
    L.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  letI : DecidableRel L.Adj := dL
  obtain ⟨Q, dQ, hQdraw, hQconn, hsub⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_6fab6ec6_c4a2_4215_b61d_4e14bbc8fe70_a2
      L dL hL hcard
  have hQ :=
    WilliamsonShmoys.connected_planar_edge_bound__p2m_6fab6ec6_c4a2_4215_b61d_4e14bbc8fe70_a1
      Q dQ hQdraw hQconn hcard
  exact le_trans (Finset.card_le_card hsub) hQ