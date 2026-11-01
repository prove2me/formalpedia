-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_2fffb22b_bc54_424c_9398_721fe1492b46_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:43:26.432891+00:00
-- url     : https://prove2.me/submissions/ed663dac-d241-4334-97cd-58446636981b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_c14196a8_6e2b_49b7_be83_e3c089778d01_a3
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_supergraph_of_hereditary__p2m_c14196a8_6e2b_49b7_be83_e3c089778d01_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      (letI : DecidableRel K.Adj := dK
       letI : DecidableRel H.Adj := dH
       K.edgeFinset ⊆ H.edgeFinset) ∧
      HasPlanarDrawingOn H ∧
      ∀ (G : SimpleGraph V) (dG : DecidableRel G.Adj),
        HasPlanarDrawingOn G →
        (letI : DecidableRel H.Adj := dH
         letI : DecidableRel G.Adj := dG
         H.edgeFinset ⊆ G.edgeFinset → H.edgeFinset = G.edgeFinset) := by
  obtain ⟨H, dH, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_supergraph_of_hereditary__p2m_c14196a8_6e2b_49b7_be83_e3c089778d01_a3
      (V := V) (K := K) (dK := dK) (P := HasPlanarDrawingOn)
      (by
        intro A B dA dB hAB hB
        exact WilliamsonShmoys.planar_drawing_subgraph__p2m_c14196a8_6e2b_49b7_be83_e3c089778d01_a3
          A B dA dB hAB hB)
      hK
  exact ⟨H, dH, hKH, hH, hmax⟩