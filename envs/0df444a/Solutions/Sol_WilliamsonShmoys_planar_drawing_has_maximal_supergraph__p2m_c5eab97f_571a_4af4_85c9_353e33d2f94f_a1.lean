-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_c5eab97f_571a_4af4_85c9_353e33d2f94f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T19:58:31.461096+00:00
-- url     : https://prove2.me/submissions/ea54e57b-b75e-4c1f-984a-a01b4ae90f7b

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_for_edge_bound_v2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ K' : SimpleGraph V, K ≤ K' →
        WilliamsonShmoys.HasPlanarDrawingOn K' → K' = K :=
  WilliamsonShmoys.planar_drawing_has_maximal_supergraph_for_edge_bound_v2 H hH hcard