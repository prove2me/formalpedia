-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_3461d3ef_e829_4302_a17d_0f8fc9f6195e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:06:14.703552+00:00
-- url     : https://prove2.me/submissions/6af75231-081c-463e-99c2-fa3e3c392c19
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_f0a3ab30_d303_4240_9967_550b6cb40a95_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_f0a3ab30_d303_4240_9967_550b6cb40a95_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : HasPlanarDrawingOn J)
    (hmax : forall K : SimpleGraph V,
      HasPlanarDrawingOn K -> J <= K -> K <= J)
    (hcard : 3 <= Fintype.card V) :
    letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    J.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
    fun K => Classical.decRel K.Adj
  have hup := WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_f0a3ab30_d303_4240_9967_550b6cb40a95_a1 J hJ hcard
  have hlo := WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_f0a3ab30_d303_4240_9967_550b6cb40a95_a1 J hJ hmax hcard
  omega