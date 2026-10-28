-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_edge_bounded_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:48:31.125914+00:00
-- url     : https://prove2.me/submissions/6e648493-4273-4184-819b-823c236fa84c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_edge_bounded_extension_maximal_drawable_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_edge_bounded_extension_maximal_edge_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨K, hNK, hKdraw, hKmax⟩ :=
    planar_graph_has_edge_bounded_extension_maximal_drawable_supergraph N hNdraw
  exact ⟨K, hNK, hKdraw,
    planar_graph_has_edge_bounded_extension_maximal_edge_bound K hKdraw hCard hKmax⟩