-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion_same_vertex_set_bound68c1edf9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T01:45:43.538007+00:00
-- url     : https://prove2.me/submissions/34b7d29e-d759-4c33-84cf-52cbbdaf7cd3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_same_vertex_set
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_completion__p2m_437ae037_6315_4598_a71b_f3c87f44dd3b_a5

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V) :
    Exists fun H : SimpleGraph V =>
      And (WilliamsonShmoys.HasPlanarDrawingOn H)
        (And (Set.Subset L.edgeSet H.edgeSet)
          (H.edgeSet.ncard + 6 = 3 * Fintype.card V)) := by
  refine Exists.elim
    (WilliamsonShmoys.planar_drawing_maximal_supergraph_same_vertex_set
      L hLdraw) ?_
  intro H hWitness
  refine Exists.intro H
    (And.intro hWitness.left (And.intro hWitness.right.left ?_))
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count_for_completion__p2m_437ae037_6315_4598_a71b_f3c87f44dd3b_a5
    H hWitness.left hWitness.right.right hCard