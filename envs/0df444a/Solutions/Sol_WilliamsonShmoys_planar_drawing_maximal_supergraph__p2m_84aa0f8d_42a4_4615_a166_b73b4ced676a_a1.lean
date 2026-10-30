-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_84aa0f8d_42a4_4615_a166_b73b4ced676a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:43:40.492154+00:00
-- url     : https://prove2.me/submissions/970306c1-c059-444b-ae6b-3d7ec60d7a23

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_hereditary_maximal_supergraph__p2m_d46620b3_b697_4ad1_8012_dcd7eecf2863_a2
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_subgraph__p2m_d46620b3_b697_4ad1_8012_dcd7eecf2863_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ G : SimpleGraph V, H ≤ G → WilliamsonShmoys.HasPlanarDrawingOn G → G ≤ H := by
  exact WilliamsonShmoys.finite_hereditary_maximal_supergraph__p2m_d46620b3_b697_4ad1_8012_dcd7eecf2863_a2
    WilliamsonShmoys.HasPlanarDrawingOn
    (by
      intro G H hGH hH
      exact WilliamsonShmoys.planarDrawingOn_subgraph__p2m_d46620b3_b697_4ad1_8012_dcd7eecf2863_a2 hGH hH)
    K hK