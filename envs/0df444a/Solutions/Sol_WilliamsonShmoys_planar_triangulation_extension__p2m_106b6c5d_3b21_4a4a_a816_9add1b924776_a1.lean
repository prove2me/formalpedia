-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_106b6c5d_3b21_4a4a_a816_9add1b924776_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:41:51.978208+00:00
-- url     : https://prove2.me/submissions/c3f6dee6-811d-4a1c-b675-fc1657dfe8df
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension__p2m_7aa49e78_992e_47a4_a47f_24fc3e2cd1e1_a2
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_card__p2m_7aa49e78_992e_47a4_a47f_24fc3e2cd1e1_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    ∃ G : SimpleGraph V,
      K.edgeFinset ⊆ G.edgeFinset ∧
      HasPlanarDrawingOn G ∧
      G.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
  obtain ⟨G, hKG, hG, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_7aa49e78_992e_47a4_a47f_24fc3e2cd1e1_a2
      K hconn hK
  exact ⟨G, hKG, hG,
    WilliamsonShmoys.edge_maximal_planar_card__p2m_7aa49e78_992e_47a4_a47f_24fc3e2cd1e1_a2
      G hG hcard hmax⟩