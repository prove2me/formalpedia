-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound__p2m_934dd260_db8f_4134_a45d_3b3ebead8b8e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:29:16.485747+00:00
-- url     : https://prove2.me/submissions/9e704e84-34fc-4207-88fc-d9722ebc4344
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_on_same_vertices__p2m_06e45311_b4a8_47cf_99af_36dad6983f39_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_euler_edge_bound__p2m_06e45311_b4a8_47cf_99af_36dad6983f39_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
    fun G => Classical.decRel G.Adj
  obtain ⟨H, hH, hsub, hmax, hle⟩ :=
    WilliamsonShmoys.maximal_planar_extension_on_same_vertices__p2m_06e45311_b4a8_47cf_99af_36dad6983f39_a1
      K hK hcard
  have hEq :=
    WilliamsonShmoys.maximal_planar_drawing_euler_edge_bound__p2m_06e45311_b4a8_47cf_99af_36dad6983f39_a1
      H hH hcard hmax
  exact le_trans hle (le_of_eq hEq)
