-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_7e43e1d3_8cc5_4078_adc3_512d6b4c19e6_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:57:51.568436+00:00
-- url     : https://prove2.me/submissions/eaa2d8da-113e-4a5f-801f-c74dfb3875d2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planarDrawing_maximal_extension__p2m_1ec71208_cc1_45fa_ad3a_a9c7012c7f6f_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_1ec71208_cc1_45fa_ad3a_a9c7012c7f6f_a3
import Theorems.Thm_WilliamsonShmoys_edgeFinset_mono__p2m_1ec71208_cc1_45fa_ad3a_a9c7012c7f6f_a3
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hconn : N.Connected) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset.card + 6 <= 3 * Fintype.card V) := by
  classical
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  change N.edgeFinset.card + 6 <= 3 * Fintype.card V
  obtain ⟨H, hNH, hHdraw, hHmax⟩ :=
    WilliamsonShmoys.planarDrawing_maximal_extension__p2m_1ec71208_cc1_45fa_ad3a_a9c7012c7f6f_a3
      N hcard hN hconn
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hHbound :=
    WilliamsonShmoys.maximal_planar_edge_bound__p2m_1ec71208_cc1_45fa_ad3a_a9c7012c7f6f_a3
      H hcard hHdraw hHmax
  have hmono :=
    WilliamsonShmoys.edgeFinset_mono__p2m_1ec71208_cc1_45fa_ad3a_a9c7012c7f6f_a3
      N H hNH
  omega