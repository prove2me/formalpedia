-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation__p2m_91b0396d_b61c_4659_90f8_b13543ceeb7a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:40:02.369262+00:00
-- url     : https://prove2.me/submissions/11dbe075-985d-4612-bff9-be1b404ad722

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_8d0b95f1_3d22_423b_9850_63148fea79a7_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count__p2m_8d0b95f1_3d22_423b_9850_63148fea79a7_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hKDrawing : HasPlanarDrawingOn K) :
    letI : ∀ L : SimpleGraph V, DecidableRel L.Adj := fun L => Classical.decRel L.Adj
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      L.edgeFinset.card = 3 * Fintype.card V - 6 := by
  classical
  letI : ∀ L : SimpleGraph V, DecidableRel L.Adj := fun L => Classical.decRel L.Adj
  obtain ⟨L, hKL, hLDrawing, hLmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_8d0b95f1_3d22_423b_9850_63148fea79a7_a1
      K hKDrawing
  refine ⟨L, hKL, hLDrawing, ?_⟩
  exact
    WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_8d0b95f1_3d22_423b_9850_63148fea79a7_a1
      L hcard hLDrawing hLmax