-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_graph_has_euler_edge_count__p2m_b5bac186_dc32_4d53_bbd2_ff87f7d5377f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:41:44.796257+00:00
-- url     : https://prove2.me/submissions/6c2b6c40-6985-4e92-a73f-b2c6723a8420
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_euler_face_incidence__p2m_4ca6b67e_a5cb_47ee_9958_b87be2ab6440_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K →
      H.edgeFinset ⊆ K.edgeFinset →
      K.edgeFinset ⊆ H.edgeFinset) :
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨f, heuler, htriangles⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_euler_face_incidence__p2m_4ca6b67e_a5cb_47ee_9958_b87be2ab6440_a1
      H dH hH hcard hmax
  omega