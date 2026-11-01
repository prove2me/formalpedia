-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6683070b_8f0f_4f85_989e_81cd2560323f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:57:30.487447+00:00
-- url     : https://prove2.me/submissions/794a2e94-e649-4a2e-967b-668c551d56e7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_extension__p2m_a4df0ed7_7cc8_4f60_8566_0ad346baef91_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet ⊆ N.edgeSet) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hNK, hK, hKcard⟩ :=
    WilliamsonShmoys.planar_graph_triangulation_extension__p2m_a4df0ed7_7cc8_4f60_8566_0ad346baef91_a1
      N hN hcard
  have hKN : K.edgeSet ⊆ N.edgeSet := hmax K hNK hK
  have hEq : N.edgeSet = K.edgeSet := Set.Subset.antisymm hNK hKN
  rw [hEq, hKcard]
