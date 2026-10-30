-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_9a006411_f424_41be_bae2_b9a9d8f6aac6_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T12:15:31.980713+00:00
-- url     : https://prove2.me/submissions/61dd0cfd-a337-4262-9387-71458e134fd6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_has_edge_maximal_planar_completion__p2m_ade061e0_083b_4a3b_882e_6784f9579cdf_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_exact_edge_count__p2m_ade061e0_083b_4a3b_882e_6784f9579cdf_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      M.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hMK, hK, hmax⟩ :=
    WilliamsonShmoys.has_edge_maximal_planar_completion__p2m_ade061e0_083b_4a3b_882e_6784f9579cdf_a1
      M hM
  exact ⟨K, hMK, hK,
    WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_ade061e0_083b_4a3b_882e_6784f9579cdf_a1
      K hK hmax hV⟩