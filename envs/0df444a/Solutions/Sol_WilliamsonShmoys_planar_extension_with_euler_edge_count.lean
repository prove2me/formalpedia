-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_with_euler_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:46:16.754816+00:00
-- url     : https://prove2.me/submissions/c6d01b92-18a7-4bbf-83a0-69e909db2153
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_9367f2ac
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_euler_edge_count_9367f2ac

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hDrawL, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension_9367f2ac K hDraw
  refine ⟨L, hKL, hDrawL, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_has_euler_edge_count_9367f2ac
    L hDrawL hMax hCard