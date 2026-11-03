-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_edge_count_lower__p2m_c5a41056_5cba_4140_8251_f29430518514_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:17:27.157576+00:00
-- url     : https://prove2.me/submissions/9aec831a-5dcb-49b5-9fa7-81b1a0efd55a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation__p2m_91b0396d_b61c_4659_90f8_b13543ceeb7a_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hKDrawing : HasPlanarDrawingOn K)
    (hKMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    letI : ∀ L : SimpleGraph V, DecidableRel L.Adj := fun L => Classical.decRel L.Adj
    3 * Fintype.card V - 6 ≤ K.edgeFinset.card := by
  classical
  obtain ⟨L, hKL, hLDrawing, hLCard⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation__p2m_91b0396d_b61c_4659_90f8_b13543ceeb7a_a1
      K hcard hKDrawing
  have hLK : L ≤ K := hKMax L hKL hLDrawing
  have hEq : K = L := le_antisymm hKL hLK
  rw [hEq]
  omega