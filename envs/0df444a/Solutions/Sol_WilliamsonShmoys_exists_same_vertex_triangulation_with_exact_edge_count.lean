-- Prove2me | solution 1 for WilliamsonShmoys.exists_same_vertex_triangulation_with_exact_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:39:35.669434+00:00
-- url     : https://prove2.me/submissions/1472c9aa-0c2f-4fd6-9615-e01db224ef88
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_same_vertex_edge_maximal_planar_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_has_exact_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V =>
      N <= K /\
      WilliamsonShmoys.HasPlanarDrawingOn K /\
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hNK, hDrawK, hMax⟩ :=
    WilliamsonShmoys.exists_same_vertex_edge_maximal_planar_extension N hDrawing
  exact ⟨K, hNK, hDrawK,
    WilliamsonShmoys.maximal_planar_has_exact_edge_count K hDrawK hCard hMax⟩