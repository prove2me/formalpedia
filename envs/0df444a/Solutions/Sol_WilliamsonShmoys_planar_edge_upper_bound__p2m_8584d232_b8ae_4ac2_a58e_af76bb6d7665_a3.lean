-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_8584d232_b8ae_4ac2_a58e_af76bb6d7665_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:56:22.481209+00:00
-- url     : https://prove2.me/submissions/2e28c36f-dcfd-40f9-841c-48cbe7b718f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_4ab90c81_e0ae_42fd_86c7_d03618200022_a2
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_4ab90c81_e0ae_42fd_86c7_d03618200022_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    N.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  obtain ⟨M, dM, hPacked⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_4ab90c81_e0ae_42fd_86c7_d03618200022_a2
      N hN hcard
  letI : DecidableRel M.Adj := dM
  rcases hPacked with ⟨hM, hmono, hconn⟩
  have hbound :=
    WilliamsonShmoys.connected_planar_edge_bound__p2m_4ab90c81_e0ae_42fd_86c7_d03618200022_a2
      M hM hconn hcard
  omega