-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_53911c92_d38e_4043_bb6e_65b3932704cd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:48:40.271682+00:00
-- url     : https://prove2.me/submissions/e2d9196a-9712-4e81-a1f1-536c9f2aa08e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_triangulated_supergraph_edge_bound__p2m_abc6942a_8a99_4355_badf_59d2c1ffe2f0_a1

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V)
    (hmax : forall K : SimpleGraph V, M <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = M) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by
  obtain ⟨K, hMK, hK, hbound⟩ :=
    WilliamsonShmoys.triangulated_supergraph_edge_bound__p2m_abc6942a_8a99_4355_badf_59d2c1ffe2f0_a1
      M hM hV
  have hEq : K = M := hmax K hMK hK
  rw [hEq] at hbound
  exact hbound