-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_2e383da1_b0fd_42ac_bf20_409641577930_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:13:26.889766+00:00
-- url     : https://prove2.me/submissions/cb7d3167-304d-477e-8ce5-55ee7672574e

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulating_extension__p2m_3c4a1050_73ac_4fb0_b659_1aa33a199ba4_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    3 * Fintype.card V - 6 ≤ K.edgeFinset.card := by
  classical
  letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
  obtain ⟨H, hKH, hHdraw, hHcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulating_extension__p2m_3c4a1050_73ac_4fb0_b659_1aa33a199ba4_a1
      K hcard hdraw
  have hHK : H = K := hmax H hKH hHdraw
  rw [← hHK]
  exact hHcard.le