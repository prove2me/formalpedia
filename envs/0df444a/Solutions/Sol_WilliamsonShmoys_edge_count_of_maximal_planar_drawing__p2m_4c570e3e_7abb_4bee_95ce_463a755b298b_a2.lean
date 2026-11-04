-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_drawing__p2m_4c570e3e_7abb_4bee_95ce_463a755b298b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:20:57.374141+00:00
-- url     : https://prove2.me/submissions/a3e93661-7090-4d2d-be9a-560db3568acd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_2a9426af_e394_457d_867f_287403a9288d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_2a9426af_e394_457d_867f_287403a9288d_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hcard : 3 ≤ Fintype.card V) (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    3 * Fintype.card V - 6 = H.edgeFinset.card := by
  letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
  have hup := WilliamsonShmoys.planar_edge_count_upper__p2m_2a9426af_e394_457d_867f_287403a9288d_a1
    hcard H hdraw
  have hlo := WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_2a9426af_e394_457d_867f_287403a9288d_a1
    hcard H hdraw hmax
  omega