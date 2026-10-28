-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_with_maximal_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:14:41.742397+00:00
-- url     : https://prove2.me/submissions/2459fca1-2431-489c-900f-49977ebcfd6d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_cc20b238_bb42_45fd_bcfd_09a78f307735
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_cc20b238_bb42_45fd_bcfd_09a78f307735

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      (∀ u v, G.Adj u v → K.Adj u v) ∧
      HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hSub, hKDraw, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_cc20b238_bb42_45fd_bcfd_09a78f307735 G hDraw
  refine ⟨K, hSub, hKDraw, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count_cc20b238_bb42_45fd_bcfd_09a78f307735 K hCard hKDraw hMax