-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_card__p2m_18dadb11_49a3_466e_95d7_24d3c5d5bdee_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:54:53.822287+00:00
-- url     : https://prove2.me/submissions/e1d8e092-20bc-4dc6-8d6e-35ece5d7cd77
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_card_upper_bound__p2m_ad845c85_bbc7_45e1_b337_b2f3a4b80492_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_ad845c85_bbc7_45e1_b337_b2f3a4b80492_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hup := WilliamsonShmoys.planar_simple_graph_edge_card_upper_bound__p2m_ad845c85_bbc7_45e1_b337_b2f3a4b80492_a1 K hK hcard
  obtain ⟨L, hKL, hL, hcardL⟩ := WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_ad845c85_bbc7_45e1_b337_b2f3a4b80492_a1 K hK hcard
  have hLK : L = K := hmax L hKL hL
  subst L
  omega