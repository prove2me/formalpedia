-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_e8e38ca1_7bc9_4d8d_a468_0001acb809e9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:46:36.175478+00:00
-- url     : https://prove2.me/submissions/1d3a8e01-2102-4d1f-8f6c-d4c3eabcb6e0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_c0a47528_8dd1_4805_9086_f86b5f89ff3f_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    3 * Fintype.card V = H.edgeFinset.card + 6 := by
  rcases WilliamsonShmoys_planar_triangulation_extension__p2m_c0a47528_8dd1_4805_9086_f86b5f89ff3f_a1
      H hH hcard with ⟨K, hHK, hK, hKcount⟩
  have hKH : K ≤ H := hmax K hHK hK
  have hEq : K = H := le_antisymm hKH hHK
  subst K
  simpa using hKcount