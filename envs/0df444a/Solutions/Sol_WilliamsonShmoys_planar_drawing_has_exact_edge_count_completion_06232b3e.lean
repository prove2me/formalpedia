-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion_06232b3e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:34:08.554845+00:00
-- url     : https://prove2.me/submissions/77c169c8-1cc0-4787-8598-694de6307943
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_638a1f84_48cf_416d_8d32_57bed5d6bb46_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_638a1f84_48cf_416d_8d32_57bed5d6bb46_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      L ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 = K.edgeSet.ncard := by
  obtain ⟨K, hLK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_638a1f84_48cf_416d_8d32_57bed5d6bb46_a2
      L hL
  exact ⟨K, hLK, hK,
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_638a1f84_48cf_416d_8d32_57bed5d6bb46_a2
      K hK hCard hmax⟩