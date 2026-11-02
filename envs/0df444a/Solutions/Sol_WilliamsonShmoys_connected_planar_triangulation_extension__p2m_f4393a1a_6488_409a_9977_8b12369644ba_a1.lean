-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_triangulation_extension__p2m_f4393a1a_6488_409a_9977_8b12369644ba_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:54:37.574179+00:00
-- url     : https://prove2.me/submissions/fafdc15b-7bdb-42b8-a63c-095a0c8d01c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_extension_maximal_supergraph__p2m_06bdf4fe_cd1d_4093_b45f_6118505c9d7e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_06bdf4fe_cd1d_4093_b45f_6118505c9d7e_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hKconn : K.Connected)
    (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       K.edgeFinset.card ≤ H.edgeFinset.card) ∧
      H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨H, hKH, hcardKH, hHconn, hHdraw, hHmax⟩ :=
    WilliamsonShmoys.planar_extension_maximal_supergraph__p2m_06bdf4fe_cd1d_4093_b45f_6118505c9d7e_a1
      K hcard hKconn hKdraw
  have hHedges :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_06bdf4fe_cd1d_4093_b45f_6118505c9d7e_a1
      H hcard hHconn hHdraw hHmax
  exact ⟨H, hKH, hcardKH, hHconn, hHdraw, hHedges⟩