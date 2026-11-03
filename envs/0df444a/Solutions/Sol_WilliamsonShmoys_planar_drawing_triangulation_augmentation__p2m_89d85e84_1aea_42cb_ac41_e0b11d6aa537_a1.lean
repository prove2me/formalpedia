-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_augmentation__p2m_89d85e84_1aea_42cb_ac41_e0b11d6aa537_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:26:25.811981+00:00
-- url     : https://prove2.me/submissions/ed9b3a42-8b90-4450-881b-4c266ee434f2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_extension__p2m_8d9b924c_10a8_4e46_9c92_7f3339daf0a6_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_edge_count__p2m_8d9b924c_10a8_4e46_9c92_7f3339daf0a6_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       3 * Fintype.card V = N.edgeFinset.card + 6) := by
  obtain ⟨N, hMN, hN, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_edge_maximal_extension__p2m_8d9b924c_10a8_4e46_9c92_7f3339daf0a6_a1
      M hM
  refine ⟨N, hMN, hN, ?_⟩
  exact WilliamsonShmoys.edge_maximal_planar_drawing_edge_count__p2m_8d9b924c_10a8_4e46_9c92_7f3339daf0a6_a1
    N hV hN hMax