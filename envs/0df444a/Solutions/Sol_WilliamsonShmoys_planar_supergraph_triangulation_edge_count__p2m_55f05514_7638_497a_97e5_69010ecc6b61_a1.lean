-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation_edge_count__p2m_55f05514_7638_497a_97e5_69010ecc6b61_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:01:45.827267+00:00
-- url     : https://prove2.me/submissions/47df8458-bf0e-4bb7-9001-d97887c92aaa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_9fcd878d_5db4_4b13_99bb_56edaa5c5ac0_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_9fcd878d_5db4_4b13_99bb_56edaa5c5ac0_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hNplanar, hNmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_9fcd878d_5db4_4b13_99bb_56edaa5c5ac0_a1
      M hM hCard
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_9fcd878d_5db4_4b13_99bb_56edaa5c5ac0_a1
      N hNplanar hNmax hCard
  exact ⟨N, hMN, hNplanar, hCount⟩