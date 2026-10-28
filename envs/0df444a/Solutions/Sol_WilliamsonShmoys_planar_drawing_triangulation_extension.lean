-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:52:21.114045+00:00
-- url     : https://prove2.me/submissions/2729586f-8636-4b0e-8a1e-08b9747b0c82
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_for_triangulation_extension_20261026
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_triangulation_extension_20261026

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, L ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hLH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_for_triangulation_extension_20261026 L hL
  have hcard :=
    WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_extension_20261026 H hH hmax hV
  exact ⟨H, hLH, hH, hcard⟩