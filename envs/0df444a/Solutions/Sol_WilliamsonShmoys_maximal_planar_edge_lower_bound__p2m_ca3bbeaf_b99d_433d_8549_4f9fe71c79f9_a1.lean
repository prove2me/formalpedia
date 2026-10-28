-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ca3bbeaf_b99d_433d_8549_4f9fe71c79f9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:58:57.276992+00:00
-- url     : https://prove2.me/submissions/eade5e5d-d974-4ff9-8840-a73cd05b852d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_9ec06c2a_4897_4f0a_9340_6489b642dcd9_a1

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V,
      N <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = N)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V <= N.edgeSet.ncard + 6 := by
  obtain ⟨K, hNK, hK, hbound⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_9ec06c2a_4897_4f0a_9340_6489b642dcd9_a1 N hN hV
  have hEq : K = N := hmax K hNK hK
  rw [hEq] at hbound
  exact hbound