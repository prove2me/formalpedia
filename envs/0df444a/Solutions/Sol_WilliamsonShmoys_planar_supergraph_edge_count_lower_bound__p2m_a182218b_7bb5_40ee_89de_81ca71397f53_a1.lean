-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_count_lower_bound__p2m_a182218b_7bb5_40ee_89de_81ca71397f53_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:45:21.199372+00:00
-- url     : https://prove2.me/submissions/73d63d9a-ecee-4551-975e-ea97e2ed35cb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_d6b9112d_6e11_42e8_8b1b_3d46cf1b698c_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_graph__p2m_d6b9112d_6e11_42e8_8b1b_3d46cf1b698c_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_d6b9112d_6e11_42e8_8b1b_3d46cf1b698c_a1
      G hcard hG
  exact ⟨K, hGK, hK,
    WilliamsonShmoys.edge_count_of_maximal_planar_graph__p2m_d6b9112d_6e11_42e8_8b1b_3d46cf1b698c_a1
      K hcard hK hmax⟩