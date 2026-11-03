-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_92fbdf79_5590_491f_9884_21ba60b9e74f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T20:08:32.887469+00:00
-- url     : https://prove2.me/submissions/67069655-4466-4123-a31e-24e116797b18

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_exact_edge_count_for_f2fc27dd
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count_for_f2fc27dd H hcard hH hmax