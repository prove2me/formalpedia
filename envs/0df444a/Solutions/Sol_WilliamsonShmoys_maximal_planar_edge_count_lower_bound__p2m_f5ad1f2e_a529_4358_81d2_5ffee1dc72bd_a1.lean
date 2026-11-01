-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_f5ad1f2e_a529_4358_81d2_5ffee1dc72bd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:58:50.763201+00:00
-- url     : https://prove2.me/submissions/bd6890dd-2d62-4385-8052-d2ac68fb4a1e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_euler_face_count__p2m_5372b848_7d0c_4e54_bcd1_c004f9c1519b_a3
import Theorems.Thm_maximal_planar_edge_count_euler_arithmetic__p2m_5372b848_7d0c_4e54_bcd1_c004f9c1519b_a3
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      3 * Fintype.card V ≤ L.edgeFinset.card + 6) := by
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_euler_face_count__p2m_5372b848_7d0c_4e54_bcd1_c004f9c1519b_a3
      L hL hcard hmax
  exact maximal_planar_edge_count_euler_arithmetic__p2m_5372b848_7d0c_4e54_bcd1_c004f9c1519b_a3
    (Fintype.card V) L.edgeFinset.card f hEuler hFaces