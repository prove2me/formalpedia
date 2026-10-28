-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_extension_fixed_vertex_type_5c9b79f9_9987_414e_a99c_5e863a94cdb9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:06:49.649256+00:00
-- url     : https://prove2.me/submissions/95085fb0-8b9e-4c5d-8c22-a772c1044906
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_fixed_vertex_type
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_fixed_vertex_type

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun H : SimpleGraph V =>
      And (K <= H) (And (WilliamsonShmoys.HasPlanarDrawingOn H)
        (3 * Fintype.card V - 6 <= H.edgeSet.ncard)) := by
  obtain ⟨H, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph_fixed_vertex_type K hK
  exact ⟨H, hKH, hH,
    WilliamsonShmoys.maximal_planar_edge_bound_fixed_vertex_type H hV hH hmax⟩