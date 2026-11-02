-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_connected_extension_triangulation__p2m_905a9a19_7f8b_412f_9275_cfdcc0758530_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:43:34.467346+00:00
-- url     : https://prove2.me/submissions/52218cd3-ee9d-478f-8246-64e5bae70271
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_extension__p2m_f4393a1a_6488_409a_9977_8b12369644ba_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_triangulation_extension__p2m_f4393a1a_6488_409a_9977_8b12369644ba_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hdisconn : ¬ N.Connected) :
    ∃ H : SimpleGraph V, N ≤ H ∧
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       N.edgeFinset.card ≤ H.edgeFinset.card) ∧
      H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨K, hNK, hcardNK, hKconn, hKdraw⟩ :=
    WilliamsonShmoys.planar_connected_extension__p2m_f4393a1a_6488_409a_9977_8b12369644ba_a1
      N hcard hN
  obtain ⟨H, hKH, hcardKH, hHconn, hHdraw, hHedges⟩ :=
    WilliamsonShmoys.connected_planar_triangulation_extension__p2m_f4393a1a_6488_409a_9977_8b12369644ba_a1
      K hcard hKconn hKdraw
  exact ⟨H, le_trans hNK hKH, Nat.le_trans hcardNK hcardKH,
    hHconn, hHdraw, hHedges⟩