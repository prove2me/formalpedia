-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_8742a5e4_f287_4b84_b71a_f78e094dd85c
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:00:36.229175+00:00
-- url     : https://prove2.me/submissions/b44cbad1-e97f-40fb-b3fa-f71a1db83899

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_edge_lower_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hMax : ∀ K : SimpleGraph V,
      J ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K = J) :
    3 * Fintype.card V - 6 ≤ J.edgeSet.ncard := by
  obtain ⟨K, hJK, hK, hBound⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_with_edge_lower_bound J hV hJ
  have hEq : K = J := hMax K hJK hK
  rw [hEq] at hBound
  exact hBound