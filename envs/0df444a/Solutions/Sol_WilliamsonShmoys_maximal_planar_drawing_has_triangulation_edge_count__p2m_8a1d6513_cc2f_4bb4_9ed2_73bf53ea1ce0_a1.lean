-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_8a1d6513_cc2f_4bb4_9ed2_73bf53ea1ce0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:17:33.12158+00:00
-- url     : https://prove2.me/submissions/876a528e-827e-495f-8bf2-66a81bcfffa7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_upper_bound__p2m_934dd260_db8f_4134_a45d_3b3ebead8b8e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_934dd260_db8f_4134_a45d_3b3ebead8b8e_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K) (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    (∀ G : SimpleGraph V, K.edgeFinset ⊆ G.edgeFinset →
      HasPlanarDrawingOn G → G = K) →
      K.edgeFinset.card + 6 = 3 * Fintype.card V := by
  intro maximal
  have hup := WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound__p2m_934dd260_db8f_4134_a45d_3b3ebead8b8e_a1
    K hK hcard
  have hlo := WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_934dd260_db8f_4134_a45d_3b3ebead8b8e_a1
    K hconn hK hcard maximal
  omega