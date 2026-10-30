-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_upper_bound__p2m_648e2563_4933_48d5_af68_a43e4e82ab0d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:17:18.454988+00:00
-- url     : https://prove2.me/submissions/af1c31ee-f27a-4756-b9da-c9024d49e9ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_a6e6652d_e481_443f_9c79_230fd6c973a0_a2
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_of_connected_supergraph__p2m_a6e6652d_e481_443f_9c79_230fd6c973a0_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hKH, hHconn, hHplanar⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_a6e6652d_e481_443f_9c79_230fd6c973a0_a2
      K hK hV
  exact
    WilliamsonShmoys.planar_edge_upper_bound_of_connected_supergraph__p2m_a6e6652d_e481_443f_9c79_230fd6c973a0_a2
      K H hKH hHconn hHplanar hV