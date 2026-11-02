-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_64226b9d_e479_429e_9ec8_cb1b67946ff3_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:37:52.21868+00:00
-- url     : https://prove2.me/submissions/e7ddd5d9-0afd-4c6c-a5eb-6c0d037ef385
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound__p2m_88aeae11_6627_4561_98a0_139448671fc8_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_88aeae11_6627_4561_98a0_139448671fc8_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hn : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      letI : DecidableRel G.Adj := dG
      letI : DecidableRel K.Adj := dK
      HasPlanarDrawingOn K →
      G.edgeFinset ⊆ K.edgeFinset →
      K.edgeFinset = G.edgeFinset) :
    letI : DecidableRel G.Adj := dG
    G.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : DecidableRel G.Adj := dG
  have hlo := WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_88aeae11_6627_4561_98a0_139448671fc8_a1
    G dG hG hn hmax
  have hhi := WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_88aeae11_6627_4561_98a0_139448671fc8_a1
    G dG hG hn
  exact le_antisymm hhi hlo