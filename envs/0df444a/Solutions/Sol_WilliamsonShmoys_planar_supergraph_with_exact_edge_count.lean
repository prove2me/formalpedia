-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_exact_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:56:13.906878+00:00
-- url     : https://prove2.me/submissions/37f4fe14-d204-4dfe-96c6-27139d4a08ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_exact_edge_count
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_exact_edge_count
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * (Fintype.card V : Int) - 6 = (L.edgeSet.ncard : Int) := by
  obtain ⟨L, hKL, hLplanar, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_for_exact_edge_count K hK
  exact ⟨L, hKL, hLplanar,
    WilliamsonShmoys.edge_count_of_maximal_planar_drawing_exact_edge_count
      L hV hLplanar hmax⟩