-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_simple_graph_edge_bound__p2m_ddf70dfc_9e43_42b2_878d_a461f3516711_a6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:49:43.547445+00:00
-- url     : https://prove2.me/submissions/cc478090-385b-42db-90a5-9659ede8e2ff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_connected__p2m_6bdbdb3d_755f_4cae_8333_ac9716c72254_a1
import Theorems.Thm_WilliamsonShmoys_planar_face_count__p2m_6bdbdb3d_755f_4cae_8333_ac9716c72254_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall L : SimpleGraph V, K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    (letI : DecidableRel K.Adj := Classical.decRel _
     K.edgeFinset.card + 6 <= 3 * Fintype.card V) := by
  letI : DecidableRel K.Adj := Classical.decRel _
  have hconn := WilliamsonShmoys.maximal_drawable_connected__p2m_6bdbdb3d_755f_4cae_8333_ac9716c72254_a1
    K hK hcard hmax
  have hdata :=
    WilliamsonShmoys.planar_face_count__p2m_6bdbdb3d_755f_4cae_8333_ac9716c72254_a1
      K hK hcard hconn
  cases hdata with
  | intro f hf =>
    cases hf with
    | intro heuler hincidence =>
      nlinarith