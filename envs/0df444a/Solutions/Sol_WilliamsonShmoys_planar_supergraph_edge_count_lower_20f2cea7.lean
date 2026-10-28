-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_count_lower_20f2cea7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:15:39.130124+00:00
-- url     : https://prove2.me/submissions/463d31a8-c270-4cb4-8f37-e1d09145d8cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_20f2cea7
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_count_20f2cea7

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hLdraw, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_20f2cea7 K hKdraw
  exact ⟨L, hKL, hLdraw,
    WilliamsonShmoys.maximal_drawable_supergraph_edge_count_20f2cea7
      L hLdraw hCard hmax⟩