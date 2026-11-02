-- Prove2me | solution 2 for WilliamsonShmoys_planar_triangulation_extension__p2m_c0a47528_8dd1_4805_9086_f86b5f89ff3f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:22:49.545376+00:00
-- url     : https://prove2.me/submissions/d32d856d-3531-4657-bd4d-d5e79f63e4b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_connected_extension__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a3
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       3 * Fintype.card V = K.edgeFinset.card + 6) := by
  classical
  obtain ⟨G, hHG, hG, hGconn⟩ :=
    WilliamsonShmoys_planar_connected_extension__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a3
      H hH hcard
  obtain ⟨K, hGK, hK, hKconn, hKmax⟩ :=
    WilliamsonShmoys_planar_maximal_extension__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a1
      G hG hGconn
  refine ⟨K, le_trans hHG hGK, hK, ?_⟩
  exact WilliamsonShmoys_maximal_planar_edge_count__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a1
    K hK hKconn hKmax hcard