-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_76f2d72e_f140_4cd7_bf10_fd0bb7e9203e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:58:50.15985+00:00
-- url     : https://prove2.me/submissions/0c637af7-3810-40ec-9d49-dfb10afdd499

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_0319396f
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_edge_count_lower_bound_0319396f H hH hmax hcard