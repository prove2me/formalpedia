-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_planar_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:18:17.750953+00:00
-- url     : https://prove2.me/submissions/0253b236-f283-4299-8ad0-c557c3069581

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_exact_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hH, hTH, hCardLE, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_finite_maximal_extension T hT hCard
  have hExact :=
    WilliamsonShmoys.maximal_planar_simple_graph_exact_edge_count H hH hMax hCard
  omega