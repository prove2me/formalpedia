-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_connected_extension__p2m_286af89a_075e_437e_a01f_e70735543bba_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:31:25.30771+00:00
-- url     : https://prove2.me/submissions/a0f90645-ab75-4c22-8ec4-633e1c814e52

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_connected_extension_triangulation__p2m_905a9a19_7f8b_412f_9275_cfdcc0758530_a1

set_option autoImplicit false

open WilliamsonShmoys

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
      H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hsub, hcard_edges, hconn, hplanar, _htriangulated⟩ :=
    WilliamsonShmoys.disconnected_planar_connected_extension_triangulation__p2m_905a9a19_7f8b_412f_9275_cfdcc0758530_a1
      N hcard hN hdisconn
  exact ⟨H, hsub, hcard_edges, hconn, hplanar⟩