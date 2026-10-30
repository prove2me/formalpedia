-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T05:35:37.195811+00:00
-- url     : https://prove2.me/submissions/053f58f9-1b5b-4fe7-a321-97ef8044eabb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_26cbec15_a016_4bbf_b55b_721eefe9b1c1_a6

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hKmax : ∀ L : SimpleGraph V, Set.Subset K.edgeSet L.edgeSet →
      HasPlanarDrawingOn L → Set.Subset L.edgeSet K.edgeSet) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition__p2m_26cbec15_a016_4bbf_b55b_721eefe9b1c1_a6
      K hK hKmax hV
  omega