-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:45:50.069516+00:00
-- url     : https://prove2.me/submissions/4f82a51b-a57c-46f7-82d0-2486adafbbe0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_for_edge_bound_562ccfc8
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_for_supergraph_562ccfc8

set_option autoImplicit false

/-- A maximal planar supergraph of a finite planar graph obeys Euler's edge bound. -/
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨K, hNK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_for_edge_bound_562ccfc8 N hN
  exact ⟨K, hNK, hK,
    WilliamsonShmoys.maximal_planar_edge_bound_for_supergraph_562ccfc8 K hV hK hmax⟩