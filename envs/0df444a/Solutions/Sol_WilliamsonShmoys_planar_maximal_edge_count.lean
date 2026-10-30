-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:58:17.903444+00:00
-- url     : https://prove2.me/submissions/c0b2dbae-4e0f-4901-a93f-1495a8c6c9ba

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_count_exists_extension_aca21fa1
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_count_for_maximal_graph_aca21fa1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : HasPlanarDrawingOn Y)
    (hCard : 3 <= Fintype.card V) :
    Exists (fun Z : SimpleGraph V =>
      And (HasPlanarDrawingOn Z)
        (And ((u v : V) -> Y.Adj u v -> Z.Adj u v)
          ((Z.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6))) := by
  obtain ⟨Z, hZ, hYZ, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_edge_count_exists_extension_aca21fa1 Y hY
  exact ⟨Z, hZ, hYZ,
    WilliamsonShmoys.planar_maximal_edge_count_for_maximal_graph_aca21fa1
      Z hZ hCard hmax⟩