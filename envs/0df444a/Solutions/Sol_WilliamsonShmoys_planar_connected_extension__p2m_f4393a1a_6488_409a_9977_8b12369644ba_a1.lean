-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_extension__p2m_f4393a1a_6488_409a_9977_8b12369644ba_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T00:49:12.450202+00:00
-- url     : https://prove2.me/submissions/5efdb3fc-1f39-4cce-8fd0-90568e66d559

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_extension
import Theorems.Thm_WilliamsonShmoys_edgeFinset_mono__p2m_f073101b_bf91_4d7c_9d90_d062f14a8fca_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       letI : DecidableRel K.Adj := Classical.decRel K.Adj
       N.edgeFinset.card ≤ K.edgeFinset.card) ∧
      K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  obtain ⟨K, hNK, hconn, hdraw, _⟩ :=
    WilliamsonShmoys.planar_connected_extension N hcard hN
  refine ⟨K, ?_, ?_, hconn, hdraw⟩
  · intro u v huv
    exact hNK u v huv
  · exact WilliamsonShmoys.edgeFinset_mono__p2m_f073101b_bf91_4d7c_9d90_d062f14a8fca_a1 N K
      (by
        intro u v huv
        exact hNK u v huv)