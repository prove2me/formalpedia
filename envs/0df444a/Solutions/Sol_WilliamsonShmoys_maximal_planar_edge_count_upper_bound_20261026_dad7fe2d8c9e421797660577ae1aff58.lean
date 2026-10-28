-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper_bound_20261026_dad7fe2d8c9e421797660577ae1aff58
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:06:19.550383+00:00
-- url     : https://prove2.me/submissions/7da37f66-1972-4efc-a9dd-c0a9cb8470b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_for_edge_bound_65502eb0_83ea_446d_8cd2_6e7ab9e51cd1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_65502eb0_83ea_446d_8cd2_6e7ab9e51cd1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hH, hKH, hmax, hle⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_for_edge_bound_65502eb0_83ea_446d_8cd2_6e7ab9e51cd1
      K hK
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count_65502eb0_83ea_446d_8cd2_6e7ab9e51cd1
      H hH hmax hV
  omega